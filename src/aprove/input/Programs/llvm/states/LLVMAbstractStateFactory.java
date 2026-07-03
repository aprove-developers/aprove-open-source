package aprove.input.Programs.llvm.states;

import java.math.*;
import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.LLVMMergeResult.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.intersecting.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.problems.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Merger.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.IntegerReasoning.smt.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Factory to create abstract LLVM states that do not emerge from existing states directly.
 * @author cryingshadow
 * @version $Id$
 */
public class LLVMAbstractStateFactory {

    /**
     * The factory to build default LLVM states.
     */
    public static final LLVMAbstractStateFactory LLVM_DEFAULT_STATE_FACTORY = new LLVMAbstractStateFactory();

    /**
     * @param newResult The merge result under construction.
     * @param allocation Some allocation.
     * @param fromOlder Is the specified allocation from the older state?
     * @return The specified allocation renamed for the merged state.
     */
    private static LLVMAllocation buildMergedAllocation(
        LLVMMergeResult newResult,
        LLVMAllocation allocation,
        boolean fromOlder
    ) {
        LLVMSimpleTerm mergedLower = LLVMAbstractStateFactory.getMergedSimpleTerm(newResult, allocation.x, fromOlder);
        LLVMSimpleTerm mergedUpper = LLVMAbstractStateFactory.getMergedSimpleTerm(newResult, allocation.y, fromOlder);
        return new LLVMAllocation(mergedLower, mergedUpper);
    }

    /**
     * Builds the merged variants of the specified allocations and adds them to the specified set for the merged state.
     * @param newResult The merge result under construction.
     * @param allocationIndices The indices of allocations in a certain stack frame or on the heap.
     * @param allocs The allocation list.
     * @param allocMapping A mapping from merged allocations to the corresponding index in the allocation list.
     * @param mergedAllocs The merged allocations.
     * @param fromOlder Is the allocation list from the older state?
     */
    private static void buildMergedAllocations(
        LLVMMergeResult newResult,
        TreeSet<Integer> allocationIndices,
        List<LLVMAllocation> allocs,
        Map<LLVMAllocation, Integer> allocMapping,
        Set<LLVMAllocation> mergedAllocs,
        boolean fromOlder
    ) {
        for (Integer newIndex : allocationIndices) {
            final LLVMAllocation mergedAlloc = LLVMAbstractStateFactory.buildMergedAllocation(newResult, allocs.get(newIndex), fromOlder);
            allocMapping.put(mergedAlloc, newIndex);
            mergedAllocs.add(mergedAlloc);
        }
    }

    /**
     * @param newResult The merge result under construction.
     * @param memory The memory information.
     * @param fromOlder Is the memory information from the older state?
     * @return A set of merged memory information entries.
     */
    private static Set<MemoryInformation> buildMergedMemory(
        LLVMMergeResult newResult,
        ImmutableMap<LLVMMemoryRange, LLVMMemoryInvariant> memory,
        boolean fromOlder
    ) {
        Set<MemoryInformation> res = new LinkedHashSet<MemoryInformation>();
        for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> entry : memory.entrySet()) {
            LLVMMemoryRange range = entry.getKey();
            LLVMMemoryInvariant invariant = entry.getValue();
            if (!(range.isPointwise() && invariant.isSimple())) {
                // TODO extend to more complex cases
                continue;
            }
            res.add(
                new MemoryInformation(
                    LLVMAbstractStateFactory.getMergedSimpleTerm(newResult, range.getFromRef(), fromOlder),
                    range.getType(),
                    range.getUnsigned(),
                    LLVMAbstractStateFactory.getMergedSimpleTerm(
                        newResult,
                        ((LLVMSimpleMemoryInvariant)invariant).getPointedToValue(),
                        fromOlder
                    )
                )
            );
        }
        return res;
    }

    /**
     * @param newResult The merge result under construction.
     * @param range Some memory range.
     * @param fromOlder Is the specified range from the older state?
     * @return The specified memory range renamed to merged variables.
     */
    private static LLVMMemoryRange buildMergedMemoryRange(
        LLVMMergeResult newResult,
        LLVMMemoryRange range,
        boolean fromOlder
    ) {
        return
            new LLVMMemoryRange(
                LLVMAbstractStateFactory.getMergedSimpleTerm(newResult, range.getFromRef(), fromOlder),
                LLVMAbstractStateFactory.getMergedSimpleTerm(newResult, range.getToRef(), fromOlder),
                range.getType(),
                range.getUnsigned()
            );
    }

    /**
     * @param newResult The merge result under construction.
     * @param rel Some relation.
     * @param fromOlder Is the specified relation from the older state?
     * @return The specified relation with renamed variables according to the merged state.
     */
    private static LLVMRelation buildMergedRelation(LLVMMergeResult newResult, LLVMRelation rel, boolean fromOlder) {
        Map<LLVMSymbolicVariable, LLVMSimpleTerm> substitution =
            new LinkedHashMap<LLVMSymbolicVariable, LLVMSimpleTerm>();
        for (LLVMSymbolicVariable var : rel.getVariables()) {
            Set<LLVMSimpleTerm> partners = newResult.getRefPartners(var, fromOlder);
            if (partners.size() > 1) {
                throw new IllegalStateException("the program variable functions are not injective!");
            }
            if (partners.size() == 1) {
                substitution.put(var, newResult.getMergedRef(partners.iterator().next(), var, fromOlder));
            }
        }
        return rel.applySubstitution(substitution);
    }

    /**
     * @param newResult The merge result under construction.
     * @param forOlder Is the substitution for the older state?
     * @return A substitution from simple terms in the specified state to ones in the merged state.
     */
    private static Map<LLVMSimpleTerm, LLVMSimpleTerm> buildMergeSubstitution(
        LLVMMergeResult newResult,
        boolean forOlder
    ) {
        Map<LLVMSimpleTerm, LLVMSimpleTerm> replacements = new LinkedHashMap<LLVMSimpleTerm, LLVMSimpleTerm>();
        for (
            Map.Entry<Pair<LLVMSimpleTerm, LLVMSimpleTerm>, LLVMSimpleTerm> entry : newResult.getRefMapping().entrySet()
        ) {
            replacements.put(forOlder ? entry.getKey().y : entry.getKey().x, entry.getValue());
        }
        return replacements;
    }

    /**
     * @param newResult The merge result under construction.
     * @param term Some simple term.
     * @param fromOlder Is the term from the older state?
     * @return If the specified term has been merged with another one, the merge result is returned. Otherwise, the
     *         term is returned unchanged.
     */
    private static LLVMSimpleTerm getMergedSimpleTerm(
        LLVMMergeResult newResult,
        LLVMSimpleTerm term,
        boolean fromOlder
    ) {
        Set<LLVMSimpleTerm> partners = newResult.getRefPartners(term, fromOlder);
        if (partners.size() > 1) {
            throw new IllegalStateException("the program variable functions are not injective!");
        }
        if (partners.isEmpty()) {
            return term;
        }
        return newResult.getMergedRef(partners.iterator().next(), term, fromOlder);
    }

    /**
     * Builds the merged allocations in both newer and older states and intersects these sets. The remaining
     * allocations are added to the generalized allocations.
     * @param newResult The merge result under construction.
     * @param newAllocIndices The allocation indices in the newer state.
     * @param newAllocs The allocation list of the newer state.
     * @param oldAllocIndices The allocation indices in the older state.
     * @param oldAllocs The allocation list of the older state.
     * @param genAllocIndices The allocation indices in the merged state.
     * @param genAllocs The allocation list of the merged state.
     * @param stackFrameIndex The index of the stack frame for the allocation or a marker for heap allocations.
     * @throws TooExpensiveException If this is too expensive.
     */
    private static void intersectMergedAllocations(
        LLVMMergeResult newResult,
        TreeSet<Integer> newAllocIndices,
        List<LLVMAllocation> newAllocs,
        TreeSet<Integer> oldAllocIndices,
        List<LLVMAllocation> oldAllocs,
        TreeSet<Integer> genAllocIndices,
        List<LLVMAllocation> genAllocs,
        int stackFrameIndex
    ) throws TooExpensiveException {
        Map<LLVMAllocation, Integer> newAllocMapping = new LinkedHashMap<LLVMAllocation, Integer>();
        Map<LLVMAllocation, Integer> oldAllocMapping = new LinkedHashMap<LLVMAllocation, Integer>();
        Set<LLVMAllocation> newFrameAllocs = new LinkedHashSet<LLVMAllocation>();
        Set<LLVMAllocation> oldFrameAllocs = new LinkedHashSet<LLVMAllocation>();
        LLVMAbstractStateFactory.buildMergedAllocations(
            newResult,
            newAllocIndices,
            newAllocs,
            newAllocMapping,
            newFrameAllocs,
            false
        );
        LLVMAbstractStateFactory.buildMergedAllocations(
            newResult,
            oldAllocIndices,
            oldAllocs,
            oldAllocMapping,
            oldFrameAllocs,
            true
        );
        Set<LLVMAllocation> res = new LinkedHashSet<LLVMAllocation>();
        for (LLVMAllocation allocation : oldFrameAllocs) {
            if (newFrameAllocs.contains(allocation)) {
                res.add(allocation);
            } else {
                newResult.addCost(LLVMCost.LOST_ALLOCATED_AREA, false);
            }
        }
        for (int i = 0; i < newFrameAllocs.size() - res.size(); i++) {
            newResult.addCost(LLVMCost.LOST_ALLOCATED_AREA, true);
        }
        for (LLVMAllocation allocation : res) {
            newResult.mergeAreas(
                newAllocMapping.get(allocation),
                oldAllocMapping.get(allocation),
                stackFrameIndex,
                true
            );
            genAllocIndices.add(genAllocs.size());
            genAllocs.add(allocation);
        }
    }

    /**
     * Merges the allocations.
     * @param newResult The merge result under construction.
     * @throws TooExpensiveException If this is too expensive.
     */
    private static void mergeAllocations(LLVMMergeResult newResult) throws TooExpensiveException {
        LLVMAbstractState newerState = newResult.getNewerState();
        LLVMAbstractState olderState = newResult.getOlderState();
        LLVMAbstractState genState = newResult.getGeneralizedState();
        Deque<LLVMReturnInformation> genCallStack = new ArrayDeque<LLVMReturnInformation>();
        List<LLVMAllocation> newAllocs = newerState.getAllocations();
        List<LLVMAllocation> oldAllocs = olderState.getAllocations();
        List<LLVMAllocation> genAllocs = new ArrayList<LLVMAllocation>();
        TreeSet<Integer> newFrameAllocs = newerState.getAllocatedInCurrentFunctionFrameIndices();
        TreeSet<Integer> oldFrameAllocs = olderState.getAllocatedInCurrentFunctionFrameIndices();
        TreeSet<Integer> genFrameAllocs = new TreeSet<Integer>();
        TreeSet<Integer> newMallocs = newerState.getAllocatedByMallocIndices();
        TreeSet<Integer> oldMallocs = olderState.getAllocatedByMallocIndices();
        TreeSet<Integer> genMallocs = new TreeSet<Integer>();
        // all three iterators must have the same number of elements
        Iterator<LLVMReturnInformation> newIt = newerState.getCallStack().iterator();
        Iterator<LLVMReturnInformation> oldIt = olderState.getCallStack().iterator();
        Iterator<LLVMReturnInformation> genIt = genState.getCallStack().iterator();
        int stackFrameIndex = 0;
        while (genIt.hasNext()) {
            LLVMReturnInformation newInfo = newIt.next();
            LLVMReturnInformation oldInfo = oldIt.next();
            LLVMReturnInformation genInfo = genIt.next();
            TreeSet<Integer> curGenFrameIndices = new TreeSet<Integer>();
            LLVMAbstractStateFactory.intersectMergedAllocations(
                newResult,
                newInfo.getAllocationsInFunction(),
                newAllocs,
                oldInfo.getAllocationsInFunction(),
                oldAllocs,
                curGenFrameIndices,
                genAllocs,
                stackFrameIndex
            );
            genCallStack.add(
                new LLVMReturnInformation(
                    genInfo.getProgramVariables(),
                    genInfo.getProgPos(),
                    ImmutableCreator.create(curGenFrameIndices)
                )
            );
            stackFrameIndex++;
        }
        LLVMAbstractStateFactory.intersectMergedAllocations(
            newResult,
            newFrameAllocs,
            newAllocs,
            oldFrameAllocs,
            oldAllocs,
            genFrameAllocs,
            genAllocs,
            stackFrameIndex
        );
        LLVMAbstractStateFactory.intersectMergedAllocations(
            newResult,
            newMallocs,
            newAllocs,
            oldMallocs,
            oldAllocs,
            genMallocs,
            genAllocs,
            LLVMMergeResult.ALLOCATION_BY_MALLOC
        );
        newResult.setGeneralizedState(
            genState.setCallStack(
                genCallStack
            ).setAllocatedMemoryForAllocaAndMalloc(
                genAllocs,
                genFrameAllocs,
                genMallocs
            )
        );
    }

    /**
     * Merges the memory information.
     * @param newResult The merge result under construction.
     * @throws TooExpensiveException If this is too expensive.
     */
    private static void mergeMemoryInformation(LLVMMergeResult newResult) throws TooExpensiveException {
        LLVMAbstractState newerState = newResult.getNewerState();
        LLVMAbstractState olderState = newResult.getOlderState();
        LLVMAbstractState genState = newResult.getGeneralizedState();
        Set<MemoryInformation> newMemory =
            LLVMAbstractStateFactory.buildMergedMemory(newResult, newerState.getMemory(), false);
        Set<MemoryInformation> oldMemory =
            LLVMAbstractStateFactory.buildMergedMemory(newResult, olderState.getMemory(), true);
        Set<MemoryInformation> res = new LinkedHashSet<MemoryInformation>();
        Set<MemoryInformation> possiblyLost = new LinkedHashSet<MemoryInformation>();
        for (MemoryInformation info : oldMemory) {
            if (newMemory.contains(info)) {
                res.add(info);
            } else {
                possiblyLost.add(info);
            }
        }
        // try to merge yet unmerged to-variables for equally merged from-variables
        Set<MemoryInformation> toDelete = new LinkedHashSet<MemoryInformation>();
        do {
            possiblyLost.removeAll(toDelete);
            toDelete.clear();
            for (MemoryInformation info : possiblyLost) {
                final Collection<LLVMSimpleTerm> mergedVariables = newResult.getRefMapping().values();
                if (!mergedVariables.contains(info.w) || mergedVariables.contains(info.z)) {
                    continue;
                }
                MemoryInformation match = null;
                for (MemoryInformation otherInfo : newMemory) {
                    if (!(info.w.equals(otherInfo.w) && info.x.equals(otherInfo.x))) {
                        continue;
                    }
                    if (match != null) {
                        // more than one match -> failure
                        match = null;
                        break;
                    }
                    if (mergedVariables.contains(otherInfo.z)) {
                        // match, but does not fit -> failure
                        break;
                    }
                    match = otherInfo;
                }
                if (match == null) {
                    continue;
                }
                final LLVMSymbolicVariable merged = newResult.mergeRefs(match.z, info.z, true);
                res.add(new MemoryInformation(info.w, info.x, info.y, merged));
                toDelete.add(info);
            }
        } while (!toDelete.isEmpty());
        // add costs for lost entries
        for (int i = 0; i < possiblyLost.size(); i++) {
            newResult.addCost(LLVMCost.LOST_HEAP_ENTRY, false);
        }
        for (int i = 0; i < newMemory.size() - res.size(); i++) {
            newResult.addCost(LLVMCost.LOST_HEAP_ENTRY, true);
        }
        Map<LLVMMemoryRange, LLVMMemoryInvariant> newHeap = new LinkedHashMap<LLVMMemoryRange, LLVMMemoryInvariant>();
        for (MemoryInformation entry : res) {
            newHeap.put(
                new LLVMMemoryRange(entry.w, entry.w, entry.x, entry.y),
                new LLVMSimpleMemoryInvariant(entry.z)
            );
        }
        newResult.setGeneralizedState(genState.setMemory(newHeap));
    }

    /**
     * @param newResult The merge result under construction.
     * @param cond The trap condition to merge.
     * @param instIsNewer Is the instance state the newer state?
     * @return The merged trap condition.
     * @throws UndefinedBehaviorException If we need to merge any variable in the specified trap condition with more
     *                                    than one other variable.
     */
    private static LLVMTrapCondition mergeTrapCondition(
        LLVMMergeResult newResult,
        LLVMTrapCondition cond,
        boolean instIsNewer
    ) throws UndefinedBehaviorException {
        LLVMTrapCondition res = cond;
        for (LLVMSymbolicVariable var : cond.getVariables()) {
            Set<LLVMSimpleTerm> varPartners = newResult.getRefPartners(var, instIsNewer);
            if (varPartners.isEmpty()) {
                // res remains unchanged
                continue;
            } else if (varPartners.size() > 1) {
                throw new TrapValueException("Need to merge two different trap conditions!");
            }
            // we have exactly one merge partner => use merged variable
            res =
                res.applySubstitution(
                    var,
                    newResult.getMergedRef(varPartners.iterator().next(), var, instIsNewer)
                );
        }
        return res;
    }

    /**
     * @param newResult The merge result under construction.
     * @param newVars A program variable function from the newer state.
     * @param oldVars A program variable function from the older state.
     * @return The merged program variable function.
     * @throws TooExpensiveException If this is too expensive.
     */
    private static Map<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> mergeVariableFunction(
        LLVMMergeResult newResult,
        ImmutableMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> newVars,
        ImmutableMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> oldVars
    ) throws TooExpensiveException {
        Map<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> res =
            new LinkedHashMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>>();
        if (!newVars.keySet().equals(oldVars.keySet())) {
            throw new TooExpensiveException("The domains of the program variable functions do not match!");
        }
        for (Map.Entry<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> entry : newVars.entrySet()) {
            String key = entry.getKey();
            ImmutablePair<LLVMSymbolicVariable, LLVMType> newValue = entry.getValue();
            ImmutablePair<LLVMSymbolicVariable, LLVMType> oldValue = oldVars.get(key);
            if (!newValue.y.equals(oldValue.y)) {
                throw new TooExpensiveException("The types of the program variables do not match!");
            }
            res.put(
                key,
                new ImmutablePair<LLVMSymbolicVariable, LLVMType>(
                    newResult.mergeRefs(newValue.x, oldValue.x, true),
                    newValue.y
                )
            );
        }
        return res;
    }

    /**
     * Merges all symbolic variables assigned to program variables in any stack frame and builds the stack frames for
     * the generalized state.
     * @param newResult The merge result under construction.
     * @throws TooExpensiveException If this is too expensive.
     */
    private static void mergeVariables(LLVMMergeResult newResult) throws TooExpensiveException {
        LLVMAbstractState newerState = newResult.getNewerState();
        LLVMAbstractState olderState = newResult.getOlderState();
        LLVMAbstractState genState =
            newResult.getGeneralizedState().setProgramVariables(
                LLVMAbstractStateFactory.mergeVariableFunction(
                    newResult,
                    newerState.getProgramVariables(),
                    olderState.getProgramVariables()
                )
            );
        // both iterators must have the same number of elements
        Iterator<LLVMReturnInformation> newIt = newerState.getCallStack().iterator();
        Iterator<LLVMReturnInformation> oldIt = olderState.getCallStack().iterator();
        Deque<LLVMReturnInformation> genCallStack = new ArrayDeque<LLVMReturnInformation>();
        while (newIt.hasNext()) {
            LLVMReturnInformation newInfo = newIt.next();
            LLVMReturnInformation oldInfo = oldIt.next();
            if (!newInfo.getProgPos().equals(oldInfo.getProgPos())) {
                throw new TooExpensiveException("Call stack not at the same position!");
            }
            // the merging of allocations is done later (in a different method)
            genCallStack.add(
                new LLVMReturnInformation(
                    ImmutableCreator.create(
                        LLVMAbstractStateFactory.mergeVariableFunction(
                            newResult,
                            newInfo.getProgramVariables(),
                            oldInfo.getProgramVariables()
                        )
                    ),
                    newInfo.getProgPos(),
                    null
                )
            );
        }
        newResult.setGeneralizedState(genState.setCallStack(genCallStack));
    }

    /**
     * @param newResult The merge result under construction.
     * @return The integer state of the older state renamed to merged variables.
     */
    private static LLVMIntegerState renameOlderStateToMerged(LLVMMergeResult newResult, Abortion aborter) {
        final LLVMIntegerState olderState = newResult.getOlderState().getIntegerState();
        final List<LLVMAllocation> allocs = new ArrayList<LLVMAllocation>();
        for (LLVMAllocation allocation : olderState.getAllocations()) {
            allocs.add(LLVMAbstractStateFactory.buildMergedAllocation(newResult, allocation, true));
        }
        final Map<LLVMSimpleTerm, LLVMSimpleTerm> substitution =
            LLVMAbstractStateFactory.buildMergeSubstitution(newResult, true);
        final Map<LLVMMemoryRange, LLVMMemoryInvariant> memory =
            new LinkedHashMap<LLVMMemoryRange, LLVMMemoryInvariant>();
        for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> entry : olderState.getMemory().entrySet()) {
            memory.put(
                LLVMAbstractStateFactory.buildMergedMemoryRange(newResult, entry.getKey(), true),
                entry.getValue().replaceReferences(substitution)
            );
        }
        final LLVMParameters params = newResult.getGeneralizedState().getStrategyParamters();
        final FrontendSMT smt = params.SMTsolver;
        final LLVMRelationFactory relationFactory = smt.stateFactory.getRelationFactory();
        final Set<IntegerRelation> rels = new LinkedHashSet<IntegerRelation>();
        for (IntegerRelation rel : olderState.toRelationSet()) {
            rels.add(
                LLVMAbstractStateFactory.buildMergedRelation(newResult, relationFactory.createRelation(rel), true)
            );
        }
        return
            new LLVMDefaultIntegerState(
                new PlainIntegerRelationState(smt.smtSolverFactory, smt.smtLogic).addRelationSet(rels, aborter),
                allocs,
                memory,
                Collections.emptyMap(),
                rels,
                params,
                aborter
            );
    }

    /**
     * Hides default constructor.
     */
    protected LLVMAbstractStateFactory() {
        // do not instantiate me from outside
    }

    /**
     * @param query The starting query.
     * @param module The LLVM module.
     * @param params Strategy parameters.
     * @return A root state with the first instruction of the function specified in the given query and information
     *         about its parameters according to that query.
     */
    public LLVMAbstractState createBeginState(LLVMQuery query, LLVMModule module, LLVMParameters params, Abortion aborter) {
        final boolean useBoundedIntegers = params.useBoundedIntegers;
        final String functionName = query.getFunction();
        LLVMFnDeclaration funcDecl = module.getFunctions().get(functionName);
        if (!(funcDecl instanceof LLVMFnDefinition)) {
            throw new IllegalArgumentException("Cannot analyze a function without its definition!");
        }
        LLVMFnDefinition function = (LLVMFnDefinition)funcDecl;
        // function parameters
        List<LLVMFnParameter> parameters = function.getParameters();
        // remember named allocated areas - pointers may be associated to the same area
        Map<String, Integer> namedAreas = new LinkedHashMap<String, Integer>();
        final int numOfParams = parameters.size();
        // the symbolic variables for the parameter variable
        LLVMSymbolicVariable[] argumentRefs = new LLVMSymbolicVariable[numOfParams];
        // the symbolic variables for size dependencies for the parameters
        LLVMSymbolicVariable[] argumentLimits = new LLVMSymbolicVariable[numOfParams];
        // the pointer types of the size dependency variables (null if the corresponding parameter is no pointer)
        LLVMPointerType[] argumentTypes = new LLVMPointerType[numOfParams];
        // marks that the first argument has an allocated area which is at least as big as the second argument (or its
        // allocated area)
        Map<Integer, Integer> argumentSizeDependencies = new LinkedHashMap<Integer, Integer>();
        final LLVMRelationFactory relationFactory = this.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        LLVMAbstractState res =
            this.emptyState(
                module,
                new LLVMProgramPosition(functionName, function.getNameOfFirstBlock(), 0),
                params,
                aborter
            );
        // TODO Should we choose another representation for global variables?
        // Note that each global variable points to an allocated area of suitable size.
        for (Map.Entry<String, LLVMGlobalVariable> e : module.getVariableDefinitions().entrySet()) {
            // Names of global variables start with @.
            final String name = "@" + e.getKey();
            LLVMGlobalVariable variable = e.getValue();
            // Create a new pointer that points to the start of some allocated area.
            res =
                this.initialKnowledgeForGlobalVariable(
                    res,
                    name,
                    variable,
                    new LLVMPointerType(variable.getType(), module.getPointerSize(), null),
                    useBoundedIntegers,
                    null,
                    aborter
                );
        }
        // check for all parameters if they are defined and if not, initialize the variables
        for (int i = 0; i < numOfParams; i++) {
            if (LLVMDebuggingFlags.SV_COMP_MODE || LLVMDebuggingFlags.TERMCOMP_MODE) {
                continue;
            }
            // TODO arrays of arrays
            LLVMFnParameter param = parameters.get(i);
            final String variableName = "%" + param.getName();
            if (Globals.useAssertions) {
                assert (!res.getProgramVariables().containsKey(variableName)) :
                    "Found two parameters with the same name!";
            }
            LLVMType type = param.getType();
            LLVMQueryInputType queryInputType = query.getType(i);
            if (queryInputType.isStringType()) {
                res =
                    this.initialKnowledgeForString(
                        res,
                        argumentRefs,
                        argumentLimits,
                        argumentTypes,
                        i,
                        variableName,
                        type,
                        queryInputType.hasMinimalSize(),
                        useBoundedIntegers,
                        null,
                        aborter
                    );
            } else if (queryInputType.isIntegerType()) {
                res =
                    this.initialKnowledgeForInteger(
                        res,
                        argumentRefs,
                        argumentLimits,
                        argumentTypes,
                        i,
                        variableName,
                        type,
                        queryInputType.getAnnotation(),
                        module.getUnsignedUnboundedVariablesPair(),
                        useBoundedIntegers,
                        null,
                        aborter
                    );
            } else if (queryInputType.isNamedAllocation()) {
                res =
                    this.initialKnowledgeForNamedArea(
                        res,
                        argumentRefs,
                        argumentLimits,
                        argumentTypes,
                        i,
                        variableName,
                        type,
                        queryInputType.getNamedArea(),
                        namedAreas,
                        useBoundedIntegers,
                        null,
                        aborter
                    );
            } else if (type.isPointerType()) {
                res =
                    this.initialKnowledgeForPointer(
                        res,
                        argumentRefs,
                        argumentLimits,
                        argumentTypes,
                        i,
                        termFactory.freshVariable(),
                        variableName,
                        (LLVMPointerType)type,
                        false,
                        useBoundedIntegers,
                        null,
                        aborter
                    );
            } else {
                LLVMSymbolicVariable var = termFactory.freshVariable();
                argumentRefs[i] = var;
                res = res.setProgramVariable(variableName, var, type);
            }
            if (queryInputType.hasMinimalSize()) {
                res =
                    this.addKnowledgeOnAllocatedSize(
                        res,
                        argumentLimits,
                        argumentTypes,
                        i,
                        queryInputType,
                        argumentSizeDependencies,
                        null,
                        aborter
                    );
            }
            // create modulo relation for alignment
            if (!res.getStrategyParamters().useOptimizations && type instanceof LLVMPointerType) {
                int align = module.getAbiAlignment(((LLVMPointerType)type).getTargetType());
                if (align > 1) {
                    if (Globals.useAssertions) {
                        // clang requires this; llvm specification seems not to be specific about it.
                        assert (IntegerUtils.isPowerOfTwo(align)) : "Alignment has to be a power of 2.";
                    }
                    LLVMRelation alignmentRel = relationFactory.createAlignmentRelation(
                                                                                        argumentRefs[i],
                                                                                        termFactory.constant(BigInteger.valueOf(align))
                                                                                    );
                    res = res.addRelation(alignmentRel, aborter);
                }
            }
        }
        return
            this.initialSizeDependencies(
                res,
                parameters,
                argumentSizeDependencies,
                argumentRefs,
                argumentLimits,
                query,
                null,
                aborter
            ).initial(aborter);
    }

    /**
     * @return The intersector for recursion handling.
     */
    public LLVMIntersector createIntersector() {
        return new LLVMIntersector();
    }

    /**
     * @return The factory to build relations.
     */
    public LLVMRelationFactory getRelationFactory() {
        return LLVMDefaultRelationFactory.LLVM_DEFAULT_RELATION_FACTORY;
    }

    /**
     * Try to merge with the states of <code>statesAtSameProgramPos</code>, where the cheapest state is chosen.
     * @param state Some state.
     * @param statesAtSameProgramPos Other states at the same program position that are candidates for a merge.
     * @param aggressive Shall we be more aggressive, i.e., still merge even if we would normally reject merging?
     * @param fastConvergence Do we think that for this state, we should add less information than usual to the generalization,
     * 			in order to speed up graph construction?
     * @param params Strategy parameters.
     * @return The best result we constructed.
     * @throws MemoryLeakException If information about mallocated memory gets lost.
     */
    public LLVMMergeResult merge(LLVMAbstractState state, Collection<LLVMAbstractState> statesAtSameProgramPos, boolean aggressive, boolean fastConvergence, Abortion aborter)
    throws MemoryLeakException {
        return this.tryToFindBetterGeneralizationResult(
            state,
            statesAtSameProgramPos,
            LLVMMergeResult.MERGING_REFERENCE_RESULT,
            aggressive,
            fastConvergence,
            aborter
        );
    }

    /**
     * Try to find a common representative of two states. Note that positive costs must be added to the merge result
     * whenever some information is not retained in either state as otherwise the recognition of instance states will
     * not work correctly (leading to overall correctness bugs).
     * @param newerState The newer state leading to the generalization.
     * @param olderState Some older state at the same program position.
     * @param bestResult The best generalization result known so far.
     * @param aggressive Shall we be more aggressive, i.e., still merge even if we would normally reject merging?
     * @param fastConvergence Do we think that for this state, we should add less information than usual to the generalization,
     * 			in order to speed up graph construction?
     * @param params Strategy parameters.
     * @return The result of this merge (automatically indicating that this was successful, as we would otherwise throw
     *         an exception).
     * @throws TooExpensiveException If merging is more expensive than in <code>bestKnownResult</code>.
     * @throws MemoryLeakException If information about mallocated memory gets lost.
     * @throws UndefinedBehaviorException If we need to merge two different trap conditions.
     */
    public LLVMMergeResult merge(LLVMAbstractState newerState, LLVMAbstractState olderState, LLVMMergeResult bestResult, boolean aggressive, boolean fastConvergence, Abortion aborter)
    throws TooExpensiveException, MemoryLeakException, UndefinedBehaviorException {
        // first, check whether the two states are compatible at all
        this.checkFormalities(newerState, olderState);
        LLVMMergeResult newResult =
            new LLVMMergeResult(bestResult, olderState, newerState, this.getRelationFactory().getTermFactory());
        // drop all knowledge from generalized state
        newResult.setGeneralizedState(newResult.getGeneralizedState().clearKnowledge(aborter));
        // merge variables - build up correspondence map
        LLVMAbstractStateFactory.mergeVariables(newResult);
        // merge remaining knowledge
        this.mergeIntegerState(newResult, newerState.getStrategyParamters(), aborter);
        this.mergeTrapValues(newResult, true);
        this.mergeTrapValues(newResult, false);

        mergeEntryStateVariableNameRecords(newResult);
        mergeAllocationChangedSinceEntryState(newResult);
        return newResult;
    }

    /**
     * Try to find a more abstract version of <code>state</code> in <code>statesAtSameProgramPos</code>.
     * @param state Some state.
     * @param statesAtSameProgramPos Other states at the same program position that are candidates for a merge.
     * @param params Strategy parameters.
     * @return The best result we constructed.
     * @throws MemoryLeakException If information about mallocated memory gets lost.
     */
    public LLVMMergeResult searchBestInstance(
        LLVMAbstractState state,
        Collection<LLVMAbstractState> statesAtSameProgramPos,
        Abortion aborter
    ) throws MemoryLeakException {
        return
            this.tryToFindBetterGeneralizationResult(
                state,
                statesAtSameProgramPos,
                LLVMMergeResult.INSTANCE_REFERENCE_RESULT,
                false,
                false,
                aborter
            );
    }

    /**
     * @param state The original state.
     * @param argumentLimits The pointers to which to add size constraints for a parameter.
     * @param argumentTypes The types of the pointers to which to add size constraints for a parameter.
     * @param i The index of the parameter.
     * @param queryInputType The query type of the parameter with index i.
     * @param argumentSizeDependencies Marks that the first argument has an allocated area which is at least as big as
     *                                 the second argument (or its allocated area).
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @return If the query type encodes a size dependency, it is added to the size dependencies and the original state
     *         is returned. If otherwise the query type encodes a positive size, the original state where the specified
     *         pointer is known to point to an address such that right from the data the specified pointer is pointing
     *         to there are at least that size many bytes to the corresponding allocation border is returned.
     *         Otherwise, just the original state is returned.
     */
    protected LLVMAbstractState addKnowledgeOnAllocatedSize(
        LLVMAbstractState state,
        LLVMSymbolicVariable[] argumentLimits,
        LLVMPointerType[] argumentTypes,
        int i,
        LLVMQueryInputType queryInputType,
        Map<Integer, Integer> argumentSizeDependencies,
        Set<LLVMRelation> newRels,
        Abortion aborter
    ) {
        final int allocatedSize = queryInputType.getMinimalSize();
        final LLVMSymbolicVariable pointer = argumentLimits[i];
        final LLVMPointerType type = argumentTypes[i];
        if (Globals.useAssertions) {
            // pointer size is irrelevant here and the parameter must be a character pointer
            assert (state.getAssociatedAllocationIndex(pointer, type, false, aborter).x != null) :
                "Found allocation size for unallocated reference!";
        }
        if (queryInputType.isSizeAnArgumentIndex()) {
            argumentSizeDependencies.put(i, allocatedSize);
        } else if (allocatedSize > 0) {
            final LLVMRelationFactory relationFactory = this.getRelationFactory();
            final LLVMTermFactory termFactory = relationFactory.getTermFactory();
            Pair<LLVMAssociationIndex, LLVMAbstractState> indexPair =
                state.getAssociatedAllocationIndex(pointer, type, false, aborter);

            LLVMRelation rel = relationFactory.lessThanEquals(
                                           termFactory.add(pointer, termFactory.constant(type.toOffset())),
                                           indexPair.y.getAllocations().get(indexPair.x.x).y
                                       );
            if (newRels != null) {
                newRels.add(rel);
            }
            return indexPair.y.addRelation(rel, aborter);
        }
        return state;
    }

    /**
     * Check the formalities:
     *  - same program position
     *  - same refinement status
     *  - no error state
     *  - same number of stack frames
     * @param newerState The newer state leading to the generalization.
     * @param olderState The older state with which we want to generalize.
     * @throws TooExpensiveException If one of the checks failed.
     */
    protected void checkFormalities(LLVMAbstractState newerState, LLVMAbstractState olderState)
    throws TooExpensiveException {
        if (!newerState.getProgramPosition().equals(olderState.getProgramPosition())) {
            throw new TooExpensiveException("States are at different program positions.");
        }
        if (newerState.isRefined() != olderState.isRefined()) {
            throw new TooExpensiveException("States have different refinement status");
        }
        if (newerState.isErrorState() || olderState.isErrorState()) {
            throw new TooExpensiveException("We do not want to merge error states!");
        }
        if (newerState.isInconsistentState() || olderState.isInconsistentState()) {
            throw new TooExpensiveException("We do not want to merge inconsistent states!");
        }
        if (newerState.getCallStack().size() != olderState.getCallStack().size()) {
            throw new TooExpensiveException("States have different number of stack frames!");
        }
    }

    /**
     * @param module The LLVM module for the state.
     * @param pos The program position for the state.
     * @param params Strategy parameters.
     * @return An empty LLVM state.
     */
    protected LLVMAbstractState emptyState(LLVMModule module, LLVMProgramPosition pos, LLVMParameters params, Abortion aborter) {
        final FrontendSMT smt = params.SMTsolver;

        LLVMDefaultIntegerState integerState = new LLVMDefaultIntegerState(
                                                new PlainIntegerRelationState(smt.smtSolverFactory, smt.smtLogic),
                                                ImmutableCreator.create(Collections.emptyList()),
                                                ImmutableCreator.create(Collections.emptyMap()),
                                                ImmutableCreator.create(Collections.emptyMap()),
                                                ImmutableCreator.create(Collections.emptySet()),
                                                params,
                                                aborter
                                            );

        return
            new LLVMAbstractState(
                module,
                ImmutableCreator.create(Collections.emptyMap()),
                ImmutableCreator.create(new TreeSet<Integer>()),
                pos,
                ImmutableCreator.create(new ArrayDeque<LLVMReturnInformation>()),
                false,
                integerState,
                false,
                ImmutableCreator.create(new TreeSet<Integer>()),
                ImmutableCreator.create(Collections.emptyMap()),
                params,
                null,
                null
            );
    }

    /**
     * @param state The original state.
     * @param name The name of the global variable.
     * @param variable The global variable.
     * @param type The type of the global variable.
     * @param useBoundedIntegers Do we use bounded integers?
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @return The original state where the specified global variable has been added including its allocation as the
     *         last allocation in the allocation list.
     */
    /**
     * @param lit An initial value of a global variable (may be <code>null</code>).
     * @return True iff <code>lit</code> is a constant scalar literal whose value can be represented as a single simple
     *         heap entry (i.e. {@link LLVMAbstractState#getSimpleTermForLiteral(LLVMLiteral)} returns its value without
     *         relying on a program variable). Aggregate initializers (arrays, structs, vectors, strings), symbolic
     *         references and <code>undef</code> are intentionally excluded: for those we keep the (sound)
     *         over-approximation of an unconstrained initial value.
     */
    private static boolean isInitializableScalarLiteral(LLVMLiteral lit) {
        return lit instanceof LLVMRegularIntLiteral
            || lit instanceof LLVMBigIntLiteral
            || lit instanceof LLVMNullLiteral
            || lit instanceof LLVMFloatLiteral
            || lit instanceof LLVMDoubleLiteral;
    }

    protected LLVMAbstractState initialKnowledgeForGlobalVariable(
        LLVMAbstractState state,
        String name,
        LLVMGlobalVariable variable,
        LLVMPointerType type,
        boolean useBoundedIntegers,
        Set<LLVMRelation> newRels,
        Abortion aborter
    ) {
        final LLVMRelationFactory relationFactory = this.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        LLVMSymbolicVariable pointer = termFactory.freshVariable();
        LLVMAbstractState res = state;
        res =
            this.initialKnowledgeForPointer(
                state,
                null,
                null,
                null,
                -1,
                pointer,
                name,
                type,
                true,
                useBoundedIntegers,
                newRels,
                aborter
            );
        // initialKnowledgeForPointer maps the global's pointer to a fresh (unconstrained) value in the heap, i.e. it
        // treats the global as uninitialized. If the global has a representable scalar initial value, overwrite that
        // heap entry with the actual initial value so that loads from the global see it (e.g. "@zero initVal: 0").
        if (LLVMAbstractStateFactory.isInitializableScalarLiteral(variable.getInitValue())) {
            final boolean unsigned;
            if (res.getStrategyParamters().useBoundedIntegers) {
                unsigned = res.getModule().getAddressesToUnsignedBitvectorVariables().contains(name);
            } else {
                unsigned = false;
            }
            res =
                res.setSimpleHeapEntry(
                    pointer,
                    type.getTargetType(),
                    unsigned,
                    res.getSimpleTermForLiteral(variable.getInitValue()),
                    aborter
                );
        }
        if (state.getModule().getAllPositions().size() < Globals.INSTRUCTION_COUNT_THRESHOLD) {
            // allocated area contains exactly the global variable
            LLVMRelation globalVarRel = relationFactory.equalTo(
                                    termFactory.add(pointer, termFactory.constant(type.toOffset())),
                                    res.getAllocations().get(res.getAllocations().size() - 1).y
                                );
            res = res.addRelation(globalVarRel, aborter);
            if (newRels != null) {
                newRels.add(globalVarRel);
            }
            // set alignment relation, if an alignment is specified
            if (!state.getStrategyParamters().useOptimizations && variable.getAlignment() != null) {
                int align = variable.getAlignment().toInt();
                if (align > 1) {
                    if (Globals.useAssertions) {
                        // clang requires this; llvm specification seems not to be specific about it.
                        assert (IntegerUtils.isPowerOfTwo(align)) : "Alignment has to be a power of 2.";
                    }
                    LLVMRelation alignmentRel = relationFactory.createAlignmentRelation(
                                                                               pointer,
                                                                               termFactory.constant(BigInteger.valueOf(align))
                                                                           );
                    res = res.addRelation(alignmentRel, aborter);
                    if (newRels != null) {
                        newRels.add(alignmentRel);
                    }
                }
            }
        }
        return res;
    }

    /**
     * @param state The original state.
     * @param argumentRefs The references for the parameters.
     * @param argumentLimits The pointers to which to add size constraints for a parameter.
     * @param argumentTypes The types of the pointers to which to add size constraints for a parameter.
     * @param i The index of the parameter.
     * @param variableName The name of the parameter variable.
     * @param type The type of the parameter variable.
     * @param annotation The integer annotation.
     * @param unsignedVariables The unsigned variables.
     * @param useBoundedIntegers Set to true if we use bounded integers.
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @return The original state where a new symbolic variable is assigned to the specified function parameter and
     *         constrained according to the specified annotation.
     */
    protected LLVMAbstractState initialKnowledgeForInteger(
        LLVMAbstractState state,
        LLVMSymbolicVariable[] argumentRefs,
        LLVMSymbolicVariable[] argumentLimits,
        LLVMPointerType[] argumentTypes,
        int i,
        String variableName,
        LLVMType type,
        LLVMIntAnnotation annotation,
        Set<Pair<String,String>> unsignedUnboundedVariables,
        boolean useBoundedIntegers,
        Set<LLVMRelation> newRels,
        Abortion aborter
    ) {
        final LLVMRelationFactory relationFactory = this.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        final LLVMSymbolicVariable var = termFactory.freshVariable();
        LLVMAbstractState res = state.setProgramVariable(variableName, var, type);
        argumentRefs[i] = var;
        argumentLimits[i] = null;
        argumentTypes[i] = null;
        final LLVMRelation newRel;
        switch (annotation) {
            case POSITIVE:
                newRel = relationFactory.positive(var);
                break;
            case NEGATIVE:
                newRel = relationFactory.negative(var);
                break;
            case NON_NEGATIVE:
                newRel = relationFactory.nonNegative(var);
                break;
            case NON_POSITIVE:
                newRel = relationFactory.nonPositive(var);
                break;
            default:
                if (!useBoundedIntegers && unsignedUnboundedVariables.contains(new Pair<String,String>(state.getCurrentFunction(),variableName))) {
                    newRel = relationFactory.nonNegative(var);
                } else {
                    newRel = null;
                }
        }
        if (newRel != null) {
            res = res.addRelation(newRel, aborter);
            if (newRels != null) {
                newRels.add(newRel);
            }
        }
        return res;
    }

    /**
     * @param state The original state.
     * @param argumentRefs The references for the parameters.
     * @param argumentLimits The pointers to which to add size constraints for a parameter.
     * @param argumentTypes The types of the pointers to which to add size constraints for a parameter.
     * @param i The index of the parameter.
     * @param variableName The name of the parameter variable.
     * @param type The type of the parameter variable.
     * @param allocName The name of the allocated area.
     * @param namedAreas The named areas.
     * @param useBoundedIntegers Set to true if we use bounded integers.
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @return The original state where a new pointer is assigned to the specified function parameter and that pointer
     *         points somewhere into the specified named allocated area. If this area has not been allocated in the
     *         original state, it is also allocated.
     */
    protected LLVMAbstractState initialKnowledgeForNamedArea(
        LLVMAbstractState state,
        LLVMSymbolicVariable[] argumentRefs,
        LLVMSymbolicVariable[] argumentLimits,
        LLVMPointerType[] argumentTypes,
        int i,
        String variableName,
        LLVMType type,
        String allocName,
        Map<String, Integer> namedAreas,
        boolean useBoundedIntegers,
        Set<LLVMRelation> newRels,
        Abortion aborter
    ) {
        final LLVMPointerType pointerType = (LLVMPointerType)type;
        final LLVMSymbolicVariable pointer = this.getRelationFactory().getTermFactory().freshVariable();
        if (namedAreas.containsKey(allocName)) {
            argumentRefs[i] = pointer;
            argumentLimits[i] = pointer;
            argumentTypes[i] = pointerType;
            return
                state.setProgramVariable(
                    variableName,
                    pointer,
                    type
                ).associateAccess(
                    pointer,
                    pointerType,
                    namedAreas.get(allocName),
                    newRels,
                    aborter
                );
        }
        LLVMAbstractState res =
            this.initialKnowledgeForPointer(
                state,
                argumentRefs,
                argumentLimits,
                argumentTypes,
                i,
                pointer,
                variableName,
                pointerType,
                false,
                useBoundedIntegers,
                newRels,
                aborter
            );
        namedAreas.put(allocName, res.getAllocations().size() - 1);
        return res;
    }

    /**
     * @param state The original state.
     * @param argumentRefs The symbolic variables for the function arguments in the initial state. If null, this
     *                     knowledge is added for a global variable.
     * @param argumentLimits The pointers to which to add size constraints for a parameter.
     * @param argumentTypes The types of the pointers to which to add size constraints for a parameter.
     * @param i The index of the function argument to add the knowledge for. Irrelevant if argumentRefs is null.
     * @param pointer The pointer to add knowledge for.
     * @param variableName The name of the parameter variable to hold the specified pointer.
     * @param type The type of the parameter variable.
     * @param pointsToStart Set to true if the created pointer should point to the start of the allocated area.
     * @param useBoundedIntegers Set to true if we use bounded integers.
     * @param termFactory The factory to build terms.
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @return The specified state where the specified variable is assigned to the specified pointer and a new
     *         allocated memory area has been added as the last one in the allocation list where the pointer is
     *         associated to. If pointsToStart is set, pointer will be identical to the lower limit of the allocated
     *         area. Otherwise, pointer will only be known to point somewhere between the allocation bounds (including
     *         these bounds).
     */
    protected LLVMAbstractState initialKnowledgeForPointer(
        LLVMAbstractState state,
        LLVMSymbolicVariable[] argumentRefs,
        LLVMSymbolicVariable[] argumentLimits,
        LLVMPointerType[] argumentTypes,
        int i,
        LLVMSymbolicVariable pointer,
        String variableName,
        LLVMPointerType type,
        boolean pointsToStart,
        boolean useBoundedIntegers,
        Set<LLVMRelation> newRels,
        Abortion aborter
    ) {
        final LLVMRelationFactory relationFactory = this.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        // we assume memory safe pointers on arbitrary fresh allocated areas
        LLVMRelation positiveRel = relationFactory.lessThanEquals(termFactory.one(), pointer);
        LLVMAbstractState res = state.addRelation(positiveRel, aborter);
        if (newRels != null) {
            newRels.add(positiveRel);
        }
        if (useBoundedIntegers) {
            LLVMRelation upperBoundRel = relationFactory.lessThanEquals(
                                                                        pointer,
                                                                        termFactory.constant(IntegerUtils.upperLimitForBoundedInt(type.size(), false))
                                                                    );
            res = res.addRelation(upperBoundRel, aborter);
            if (newRels != null) {
                newRels.add(upperBoundRel);
            }
        }
        // we interpret a memory area bound as an i8 pointer
        LLVMSymbolicVariable lower = pointsToStart ? pointer : termFactory.freshVariable();
        LLVMSymbolicVariable upper = termFactory.freshVariable();
        if (argumentRefs != null) {
            argumentRefs[i] = pointer;
            argumentLimits[i] = pointer;
            argumentTypes[i] = type;
        }
        /*
         * Allocate initial memory on the lowest stack frame. Although this is not what usually happens, for our
         * analysis it has the right effect: It is allocated everywhere (since the lowest stack frame is visible
         * everywhere) and one cannot safely call free on it (since it is not declared as allocated by malloc). If we
         * want to model this more precisely, we need an additional allocation marker for initial memory allocations
         * (or the possibility to add allocations without any marker).
         */
        boolean unsigned;
        if (res.getStrategyParamters().useBoundedIntegers) {
            unsigned = res.getModule().getAddressesToUnsignedBitvectorVariables().contains(variableName);
        } else {
            unsigned = false;
        }
        final LLVMSymbolicVariable freshVar = this.getRelationFactory().getTermFactory().freshVariable();
        return
            res.allocateMemoryAndAssociatePointer(
                lower,
                upper,
                pointer,
                type,
                true,
                newRels,
                aborter
            ).setProgramVariable(
                variableName,
                pointer,
                type
            ).setSimpleHeapEntry(
                pointer,
                type.getTargetType(),
                unsigned,
                freshVar,
                aborter
            );
    }

    /**
     * @param state The original state.
     * @param argumentRefs The argument variables for the initial state.
     * @param argumentLimits The pointers to which to add size constraints for a parameter.
     * @param argumentTypes The types of the pointers to which to add size constraints for a parameter.
     * @param i The index of the argument variable to add the knowledge for.
     * @param variableName The name of the parameter variable.
     * @param type The type of the parameter variable.
     * @param minimalSizeNonNegative Is there additional allocated space after the terminating 0?
     * @param useBoundedIntegers Set to true if we use bounded integers.
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @return The original state where the knowledge has been added that the argument with index i points to an
     *         allocated string. The array of argument variables is updated such that the entry at index i is the
     *         corresponding pointer.
     */
    protected LLVMAbstractState initialKnowledgeForString(
        LLVMAbstractState state,
        LLVMSymbolicVariable[] argumentRefs,
        LLVMSymbolicVariable[] argumentLimits,
        LLVMPointerType[] argumentTypes,
        int i,
        String variableName,
        LLVMType type,
        boolean minimalSizeNonNegative,
        boolean useBoundedIntegers,
        Set<LLVMRelation> newRels,
        Abortion aborter
    ) {
        if (Globals.useAssertions) {
            assert (type.isPointerType()) : "Argument should be a string, but is no pointer!";
            assert (((LLVMPointerType)type).getTargetType().isIntTypeOfSize(8)) : "Argument should be a "
                + "string, but does not point to i8!";
        }
        final LLVMTermFactory termFactory = this.getRelationFactory().getTermFactory();
        final LLVMPointerType pointerType = (LLVMPointerType)type;
        final LLVMSymbolicVariable pointer = termFactory.freshVariable();
        LLVMAbstractState res =
            this.initialKnowledgeForPointer(
                state,
                argumentRefs,
                argumentLimits,
                argumentTypes,
                i,
                pointer,
                variableName,
                pointerType,
                true,
                useBoundedIntegers,
                newRels,
                aborter
            );
        final int index = res.getAllocations().size() - 1;
        final LLVMSymbolicVariable upperAllocationBound = (LLVMSymbolicVariable)res.getAllocations().get(index).y;
        final LLVMSymbolicVariable refToZero;
        if (minimalSizeNonNegative) {
            // additional space allocated after terminating 0
            refToZero = termFactory.freshVariable();
        } else {
            refToZero = upperAllocationBound;
        }
        argumentLimits[i] = refToZero;
        argumentTypes[i] = pointerType;
        return
            res.setSimpleHeapEntry(
                refToZero,
                LLVMIntType.I8,
                false,
                termFactory.zero(),
                aborter
            ).associateAccess(
                refToZero,
                pointerType,
                index,
                newRels,
                aborter
            );
    }

    /**
     * Handle size dependencies.
     * @param state The original state.
     * @param parameters The parameters.
     * @param argumentSizeDependencies The argument size dependencies.
     * @param argumentRefs The argument references.
     * @param argumentLimits The limit references for the parameters.
     * @param query The query to ask whether some argument is a String.
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @return The original state where information about size dependencies is added.
     */
    protected LLVMAbstractState initialSizeDependencies(
        LLVMAbstractState state,
        List<LLVMFnParameter> parameters,
        Map<Integer, Integer> argumentSizeDependencies,
        LLVMSymbolicVariable[] argumentRefs,
        LLVMSymbolicVariable[] argumentLimits,
        LLVMQuery query,
        Set<LLVMRelation> newRels,
        Abortion aborter
    ) {
        final LLVMRelationFactory relationFactory = this.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        LLVMAbstractState res = state;
        for (Map.Entry<Integer, Integer> dependency : argumentSizeDependencies.entrySet()) {
            // firstArg depends on secondArg (usually firstArg is at least as big as secondArg)
            final int firstArg = dependency.getKey();
            final int secondArg = dependency.getValue();
            final LLVMType secondType = parameters.get(secondArg).getType();
            final LLVMSymbolicVariable firstRef = argumentLimits[firstArg];
            final LLVMSymbolicVariable secondRef = argumentRefs[secondArg];
            final LLVMPointerType firstType = (LLVMPointerType)parameters.get(firstArg).getType();
            final Pair<LLVMAssociationIndex, LLVMAbstractState> indexPair =
                res.getAssociatedAllocationIndex(firstRef, firstType, false, aborter);
            res = indexPair.y;
            final Integer indexForFirst = indexPair.x.x;
            if (secondType.isPointerType()) {
                final Pair<LLVMAssociationIndex, LLVMAbstractState> secondIndexPair =
                    res.getAssociatedAllocationIndex(secondRef, (LLVMPointerType)secondType, false, aborter);
                res = secondIndexPair.y;
                Integer indexForSecond = secondIndexPair.x.x;
                LLVMSimpleTerm firstUpper = res.getAllocations().get(indexForFirst).y;
                LLVMSimpleTerm secondUpper = res.getAllocations().get(indexForSecond).y;
                /*
                 * Note that this is also true for Strings as terminating 0 is not duplicated!
                 * firstRef + secondUpper - secondRef <= firstUpper
                 * <=>
                 * firstRef + secondUpper <= secondRef + firstUpper
                 */
                LLVMRelation rel = relationFactory.lessThanEquals(
                                                                  termFactory.add(firstRef, secondUpper),
                                                                  termFactory.add(secondRef, firstUpper)
                                                              );
                res = res.addRelation(rel, aborter);
                if (newRels != null) {
                    newRels.add(rel);
                }
            } else if (secondType.isIntType()) {
                // firstRef is at least secondRef * byteSize (- 1) bytes away from its upper allocation limit
                // so add relation firstRef + byteSize*secondRef <= upperBound (+ 1)
                LLVMRelation rel = relationFactory.lessThanEquals(
                                                                  termFactory.add(
                                                                                  firstRef,
                                                                                  termFactory.mult(
                                                                                      termFactory.constant(
                                                                                          IntegerUtils.bitsToBytes(firstType.getTargetType().size())
                                                                                      ),
                                                                                      secondRef
                                                                                  )
                                                                              ),
                                                                              termFactory.add(
                                                                                  res.getAllocations().get(indexForFirst).y,
                                                                                  query.getType(firstArg).isStringType() ? termFactory.zero() : termFactory.one()
                                                                              )
                                                                          );

                res = res.addRelation(rel, aborter);
                if (newRels != null) {
                    newRels.add(rel);
                }
            } else {
                throw new IllegalArgumentException(
                    "Size dependency on an argument which is neither a pointer nor an integer!"
                );
            }
        }
        return res;
    }

    /**
     * Merges the trap values. This should only be done after all symbolic variables have been merged.
     * @param newResult The merge result under construction.
     * @param instIsNewer Is the instance state the newer state?
     * @throws UndefinedBehaviorException If we need to merge two different trap conditions or if two trap values are
     *                                    merged to a constant (the latter should never happen, actually).
     */
    protected void mergeTrapValues(LLVMMergeResult newResult, boolean instIsNewer) throws UndefinedBehaviorException {
        LLVMAbstractState instState = newResult.getInstState(instIsNewer);
        LLVMAbstractState ofState = newResult.getOfState(instIsNewer);
        LLVMAbstractState genState = newResult.getGeneralizedState();
        Set<LLVMSymbolicVariable> varsInGen = genState.getSymbolicVariables();
        Map<LLVMSymbolicVariable, LLVMTrapCondition> trapVals =
            new LinkedHashMap<LLVMSymbolicVariable, LLVMTrapCondition>(newResult.getGeneralizedState().getTrapValues());
        for (Map.Entry<LLVMSymbolicVariable, LLVMTrapCondition> entry : ofState.getTrapValues().entrySet()) {
            LLVMSymbolicVariable trap = entry.getKey();
            Set<LLVMSimpleTerm> partners = newResult.getRefPartners(trap, instIsNewer);
            if (partners.isEmpty()) {
                if (!varsInGen.contains(trap)) {
                    continue;
                }
                trapVals.put(
                    trap,
                    LLVMAbstractStateFactory.mergeTrapCondition(newResult, entry.getValue(), instIsNewer)
                );
            } else {
                LLVMTrapCondition cond =
                    LLVMAbstractStateFactory.mergeTrapCondition(newResult, entry.getValue(), instIsNewer);
                for (LLVMSimpleTerm partner : partners) {
                    if (
                        instState.isPossiblyTrapValue(partner)
                        && !cond.equals(
                            LLVMAbstractStateFactory.mergeTrapCondition(
                                newResult,
                                instState.getTrapValues().get(partner),
                                !instIsNewer
                            )
                        )
                    ) {
                        throw new TrapValueException("Need to merge two different trap conditions!");
                    }
                    LLVMSimpleTerm merged = newResult.getMergedRef(partner, trap, instIsNewer);
                    if (merged instanceof LLVMSymbolicVariable) {
                        trapVals.put((LLVMSymbolicVariable)merged, cond);
                    } else {
                        throw new TrapValueException("Merging of trap values would lead to constant trap value!");
                    }
                }
            }
        }
        newResult.setGeneralizedState(genState.setTrapValues(trapVals));
    }

    /**
     * Try to merge <code>state</code> with the states of <code>statesAtSameProgramPos</code>, but
     * abort when the result is worse (i.e., more costly) than <code>refResult</code>.
     * @param state Some state.
     * @param statesAtSameProgramPos Other states at the same program position that are candidates for a merge.
     * @param refResult The reference result whose costs should not be exceeded.
     * @param aggressive Shall we be more aggressive, i.e., still merge even if we would normally reject merging?
     * @param fastConvergence Do we think that for this state, we should add less information than usual to the generalization,
     * 			in order to speed up graph construction?
     * @param params Strategy parameters.
     * @return The best result we constructed.
     * @throws MemoryLeakException If information about mallocated memory gets lost.
     */
    protected LLVMMergeResult tryToFindBetterGeneralizationResult(
        LLVMAbstractState state,
        Collection<LLVMAbstractState> statesAtSameProgramPos,
        LLVMMergeResult refResult,
        boolean aggressive,
        boolean fastConvergence,
        Abortion aborter
    ) throws MemoryLeakException {
        LLVMMergeResult bestResult = refResult;
        for (LLVMAbstractState olderState : statesAtSameProgramPos) {
            try {
                bestResult = this.merge(state, olderState, bestResult, aggressive, fastConvergence, aborter);
            } catch (TooExpensiveException | UndefinedBehaviorException e) {
                // this is just ignored.
                continue;
            }
        }
        return bestResult;
    }

    /**
     * Adds the relations x1 - y1 (<=/=/>=) (z1 / z2) * (x2 - y2) to the specified set if these are implied in the
     * other state. The specified distance patterns must satisfy the condition z1 % z2 == 0.
     * @param newResult The merge result under construction.
     * @param renamedState The older state renamed to merged variables.
     * @param pattern Some distance pattern x1 - y1 = z1.
     * @param otherPattern Another distance pattern x2 - y2 = z2.
     * @param res A set of relations.
     */
    private void addDistanceRelations(
        LLVMMergeResult newResult,
        LLVMIntegerState renamedState,
        DistancePattern pattern,
        DistancePattern otherPattern,
        Set<LLVMRelation> res,
        Abortion aborter
    ) {
        final LLVMTermFactory termFactory = this.getRelationFactory().getTermFactory();
        BigInteger constant = pattern.z.divide(otherPattern.z);
        final LLVMTerm sub1 = termFactory.sub(pattern.x, pattern.y);
        final LLVMTerm sub2 = termFactory.sub(otherPattern.x, otherPattern.y);
        if (constant.compareTo(BigInteger.ONE) == 0) {
            this.addDistanceRelations(newResult, renamedState, sub1, sub2, res, aborter);
        } else {
            this.addDistanceRelations(
                newResult,
                renamedState,
                sub1,
                termFactory.mult(termFactory.constant(constant), sub2),
                res,
                aborter
            );
        }
    }

    /**
     * Adds the relations exp1 (<=/=/>=) exp2 to the specified set if these are implied in the other state.
     * @param newResult The merge result under construction.
     * @param renamedState The older state renamed to merged variables.
     * @param exp1 Some term.
     * @param exp2 Another term.
     * @param res A set of relations.
     */
    private void addDistanceRelations(
        LLVMMergeResult newResult,
        LLVMIntegerState renamedState,
        LLVMTerm exp1,
        LLVMTerm exp2,
        Set<LLVMRelation> res,
        Abortion aborter
    ) {
        final LLVMRelationFactory relationFactory = this.getRelationFactory();
        final LLVMRelation eq =
            LLVMAbstractStateFactory.buildMergedRelation(newResult, relationFactory.equalTo(exp1, exp2), false);
        final LLVMRelation leq =
            LLVMAbstractStateFactory.buildMergedRelation(newResult, relationFactory.lessThanEquals(exp1, exp2), false);
        final LLVMRelation geq =
            LLVMAbstractStateFactory.buildMergedRelation(newResult, relationFactory.lessThanEquals(exp2, exp1), false);
        if (renamedState.checkRelation(eq, aborter).x) {
            res.add(eq);
            res.add(leq);
            res.add(geq);
        } else if (renamedState.checkRelation(leq, aborter).x) {
            res.add(leq);
        } else if (renamedState.checkRelation(geq, aborter).x) {
            res.add(geq);
        }
    }

    /**
     * Merges the integer states including allocations and memory information.
     * @param newResult The merge result under construction.
     * @param params Strategy parameters.
     * @throws TooExpensiveException If this is too expensive.
     */
    private void mergeIntegerState(LLVMMergeResult newResult, LLVMParameters params, Abortion aborter) throws TooExpensiveException {
        // first, merge memory information as that might lead to further merging of variables
        LLVMAbstractStateFactory.mergeMemoryInformation(newResult);
        LLVMAbstractStateFactory.mergeAllocations(newResult);
        this.mergeRelations(newResult, params, aborter);
    }

    /**
     * Merges the relations.
     * @param newResult The merge result under construction.
     * @param params Strategy parameters.
     * @throws TooExpensiveException If this is too expensive.
     */
    private void mergeRelations(LLVMMergeResult newResult, LLVMParameters params, Abortion aborter) throws TooExpensiveException {
        final LLVMRelationFactory relationFactory = this.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        LLVMAbstractState newerState = newResult.getNewerState();
        LLVMAbstractState olderState = newResult.getOlderState();
        IntegerRelationSet aDiamond = newerState.getIntegerState().toRelationSet();
        Set<LLVMRelation> aDoubleDiamond = new LinkedHashSet<LLVMRelation>();
        for (IntegerRelation rel : aDiamond) {
            aDoubleDiamond.add(relationFactory.createRelation(rel));
        }
        for (IntegerRelation rel : aDiamond.getEquations()) {
            LLVMTerm lhs = termFactory.create(rel.getLhs());
            LLVMTerm rhs = termFactory.create(rel.getRhs());
            aDoubleDiamond.add(relationFactory.lessThanEquals(lhs, rhs));
            aDoubleDiamond.add(relationFactory.lessThanEquals(rhs, lhs));
        }
        for (IntegerRelation rel : aDiamond.getUndirectedInequalities()) {
            LLVMTerm lhs = termFactory.create(rel.getLhs());
            LLVMTerm rhs = termFactory.create(rel.getRhs());
            LLVMRelation lt = relationFactory.lessThan(lhs, rhs);
            if (newerState.checkRelation(lt, aborter).x) {
                aDoubleDiamond.add(lt);
            } else {
                LLVMRelation gt = relationFactory.lessThan(rhs, lhs);
                if (newerState.checkRelation(gt, aborter).x) {
                    aDoubleDiamond.add(gt);
                }
            }
        }
        Set<LLVMRelation> missing = new LinkedHashSet<LLVMRelation>();
        Set<LLVMRelation> res = new LinkedHashSet<LLVMRelation>();
        LLVMIntegerState renamedState = LLVMAbstractStateFactory.renameOlderStateToMerged(newResult, aborter);
        for (LLVMRelation rel : aDoubleDiamond) {
            final LLVMRelation renamedRel = LLVMAbstractStateFactory.buildMergedRelation(newResult, rel, false);
            if (renamedState.checkRelation(renamedRel, aborter).x) {
                res.add(renamedRel);
            } else {
                missing.add(rel);
                newResult.addCost(LLVMCost.LOST_RELATION, true);
            }
        }
        for (LLVMRelation rel : missing) {
            DistancePattern pattern = this.toDistancePattern(rel, params, aborter);
            if (pattern == null) {
                continue;
            }
            for (LLVMRelation otherRel : missing) {
                if (rel == otherRel) {
                    continue;
                }
                DistancePattern otherPattern = this.toDistancePattern(otherRel, params, aborter);
                if (otherPattern == null) {
                    continue;
                }
                if (pattern.z.abs().remainder(otherPattern.z.abs()).compareTo(BigInteger.ZERO) == 0) {
                    this.addDistanceRelations(newResult, renamedState, pattern, otherPattern, res, aborter);
                } else if (otherPattern.z.abs().remainder(pattern.z.abs()).compareTo(BigInteger.ZERO) == 0) {
                    this.addDistanceRelations(newResult, renamedState, otherPattern, pattern, res, aborter);
                }
            }
        }
        LLVMAbstractState genState = newResult.getGeneralizedState();
        LLVMIntegerState iState =
            genState.getIntegerState().addRelationSet(res, aborter);
        if (iState instanceof LLVMDefaultIntegerState) {
            iState = ((LLVMDefaultIntegerState)iState).updateFormula(aborter).x;
        }
        genState = genState.setIntegerState(iState);
        // add costs for older state
        for (IntegerRelation rel : olderState.getIntegerState().toRelationSet()) {
            final Pair<Boolean, ? extends LLVMAbstractState> check =
                genState.checkRelation(
                    LLVMAbstractStateFactory.buildMergedRelation(newResult, relationFactory.createRelation(rel), true),
                    aborter
                );
            genState = check.y;
            if (!check.x) {
                newResult.addCost(LLVMCost.LOST_RELATION, false);
            }
        }
        newResult.setGeneralizedState(genState);
    }

    /**
     * @param relation Some relation.
     * @param params Strategy parameters.
     * @return A triple (x,y,z) if the specified relation implies x - y = z for two variables x and y and a constant z.
     *         Null otherwise.
     * @throws TooExpensiveException If this is too expensive.
     */
    private DistancePattern toDistancePattern(IntegerRelation relation, LLVMParameters params, Abortion aborter)
    throws TooExpensiveException {
        if (!relation.isEquation()) {
            return null;
        }
        final LLVMRelationFactory relationFactory = this.getRelationFactory();
        final LLVMTermFactory termFactory = relationFactory.getTermFactory();
        LLVMRelation rel = relationFactory.createRelation(relation);
        final Set<? extends LLVMSymbolicVariable> vars = rel.getVariables();
        if (vars.size() != 2) {
            return null;
        }
        final Substitution sigma =
            new Substitution() {

                @Override
                public Expression substitute(Variable v) {
                    if (vars.contains(v)) {
                        return termFactory.zero();
                    }
                    return v;
                }

            };
        final LLVMConstant constant;
        try {
            constant =
                ((LLVMTerm)termFactory.sub(rel.getLhs(), rel.getRhs()).applySubstitution(sigma)).evaluate(termFactory);
        } catch (DivisionByZeroException e) {
            throw new TooExpensiveException(e.getMessage());
        }
        if (constant == null || constant.equals(termFactory.zero())) {
            return null;
        }
        Iterator<? extends LLVMSymbolicVariable> it = vars.iterator();
        LLVMSymbolicVariable var1 = it.next();
        LLVMSymbolicVariable var2 = it.next();
        final FrontendSMT smt = params.SMTsolver;
        IntegerState state = new PlainIntegerRelationState(smt.smtSolverFactory, smt.smtLogic);
        state = state.addRelation(relation, aborter);
        final LLVMTerm sub1 = termFactory.sub(var1, var2);
        final LLVMTerm sub2 = termFactory.sub(var2, var1);
        final LLVMConstant neg = constant.negate();
        if (state.checkRelation(relationFactory.equalTo(sub1, constant), aborter).x) {
            return new DistancePattern(var1, var2, constant.getIntegerValue());
        } else if (state.checkRelation(relationFactory.equalTo(sub2, constant), aborter).x) {
            return new DistancePattern(var2, var1, constant.getIntegerValue());
        } else if (state.checkRelation(relationFactory.equalTo(sub1, neg), aborter).x) {
            return new DistancePattern(var1, var2, neg.getIntegerValue());
        } else if (state.checkRelation(relationFactory.equalTo(sub2, neg), aborter).x) {
            return new DistancePattern(var2, var1, neg.getIntegerValue());
        }
        return null;
    }


    protected static void mergeAllocationChangedSinceEntryState(LLVMMergeResult newResult) throws TooExpensiveException {
    	LLVMAbstractState olderState = newResult.getOlderState();
    	LLVMAbstractState newerState = newResult.getNewerState();

    	boolean isStartOfFunction = olderState.getProgramPosition().isFunctionStart(olderState.getModule());


    	ImmutableMap<Integer,Boolean> olderStateMap = olderState.getAllocationChangedSinceEntryStateMap();
    	ImmutableMap<Integer,Boolean> newerStateMap = newerState.getAllocationChangedSinceEntryStateMap();


    	if((olderStateMap == null && newerStateMap == null) || olderState.getCallStack().isEmpty() && isStartOfFunction) {
    		//We don't do anything for these kinds of states

    		return;
    	}



    	if((olderStateMap == null) != (newerStateMap == null)) {
    		throw new IllegalStateException("When merging states, one of them had an allocation change map, but the other did not!");
    	}

    	if(newResult.getGeneralizedState().getAllocations().size() != newResult.getNumberOfMergedAreas()) {
    		throw new IllegalStateException("Allocation count mismatch!");
        }

    	Map<Integer,Boolean> mutableResultMap = new LinkedHashMap<>();


    	for (int mergedIndex = 0; mergedIndex < newResult.getNumberOfMergedAreas(); mergedIndex++) {
            AllocationMapping indices = newResult.getAllocationMappingForMergedIndex(mergedIndex, true);
            if (Globals.useAssertions) {
                assert (indices != null ) : "Found merged index without source indices!";
            }

            Boolean newerStateEntry = newerStateMap.get(indices.x);
            Boolean olderStateEntry = olderStateMap.get(indices.y);

            Integer mergeAllocationIndex = indices.z;

            if(olderStateEntry != null || newerStateEntry != null) {
            	if(olderStateEntry == null && newerStateEntry != null) {
            		newResult.addCost(LLVMCost.LOST_ALLOCATED_AREA, false);
            	} else if(olderStateEntry != null && newerStateEntry == null) {
            		newResult.addCost(LLVMCost.LOST_ALLOCATED_AREA, true);
            	} else {
            		if(newerStateEntry == olderStateEntry) {
            			//same boolean result
            			mutableResultMap.put(mergeAllocationIndex, newerStateEntry);
            		} else {
            			//different boolean result:
            			if(newerStateEntry) {
            				//olderStateEbntry must be false
            				newResult.addCost(LLVMCost.LOST_ALLOCATED_AREA, false);
            			} else {
            				//olderStateEbntry must be true
            				newResult.addCost(LLVMCost.LOST_ALLOCATED_AREA, true);
            			}
            			mutableResultMap.put(mergeAllocationIndex, true);

            		}
            	}
            }

        }

    	ImmutableMap<Integer,Boolean> immutableResultMap = ImmutableCreator.create(mutableResultMap);
    	newResult.setGeneralizedState(newResult.getGeneralizedState().setAllocationChangedSinceEntryState(immutableResultMap));

    }

    /**
     * If present, merge the entry state variable correspondences of both states.
     *
     * We do not do so for potential entry states (i.e., states with a single stack frame at the beginning of a function)
     *
     * If x -> [v,w] and x -> [u,z] are mappings in the newer/older state (i.e., x is an entry state variable)
     * then the merged state gets the mapping x -> p([v,w]) \cap q([u,z]),
     * where p maps variables from the newer state to the generalized state and q from the older to generalized state.
     *
     *
     * @param newResult
     * @throws TooExpensiveException
     */
    protected static void mergeEntryStateVariableNameRecords(LLVMMergeResult newResult) throws TooExpensiveException {
    	LLVMAbstractState olderState = newResult.getOlderState();
    	LLVMAbstractState newerState = newResult.getNewerState();

    	boolean isStartOfFunction = olderState.getProgramPosition().isFunctionStart(olderState.getModule());

    	if(olderState.getCallStack().isEmpty() && isStartOfFunction) {
    		//We don't do anything for these kinds of states

    		return;
    	}

    	ImmutableMap<LLVMSymbolicVariable,ImmutableSet<LLVMSymbolicVariable>> olderStateMap =
    			olderState.getEntryStateVarCorrespondenceMap();

    	ImmutableMap<LLVMSymbolicVariable,ImmutableSet<LLVMSymbolicVariable>> newerStateMap =
    			newerState.getEntryStateVarCorrespondenceMap();

    	if(olderStateMap == null && newerStateMap == null) {
    		//the states don't want any tracking

    		return;
    	}

    	if(!(olderStateMap != null && newerStateMap != null)) {
    		throw new IllegalStateException("One State has entry state var map, but the other does not.");
    	}



    	Map<Pair<LLVMSimpleTerm, LLVMSimpleTerm>, LLVMSimpleTerm> refMapping  = newResult.getRefMapping();
    	Map<LLVMSimpleTerm, Set<LLVMSimpleTerm>> olderToGenRefMap = new LinkedHashMap<>();
    	Map<LLVMSimpleTerm, Set<LLVMSimpleTerm>> newertoGenRefMap = new LinkedHashMap<>();

    	refMapping.forEach( (k,v) ->  {
    		newertoGenRefMap.computeIfAbsent(k.x, u -> new LinkedHashSet<>()).add(v);
    		olderToGenRefMap.computeIfAbsent(k.y, u -> new LinkedHashSet<>()).add(v);
    			});


    	Set<LLVMSymbolicVariable> entryStateVars = new LinkedHashSet<>();
    	entryStateVars.addAll(olderStateMap.keySet());
    	entryStateVars.addAll(newerStateMap.keySet());


    	Map<LLVMSymbolicVariable,ImmutableSet<LLVMSymbolicVariable>> resultMutable = new LinkedHashMap<>();

    	for(LLVMSymbolicVariable entryStateVar :  entryStateVars) {
    		ImmutableSet<LLVMSymbolicVariable> olderStateVars = olderStateMap.get(entryStateVar);
    		if(olderStateVars == null) {
    			newResult.addCost(LLVMCost.WEAKER_RELATION, false);
    			continue;
    		}


    		ImmutableSet<LLVMSymbolicVariable> newerStateVars = newerStateMap.get(entryStateVar);
    		if(newerStateVars == null) {
    			newResult.addCost(LLVMCost.WEAKER_RELATION, true);
    			continue;
    		}

    		if(olderStateVars.isEmpty() || newerStateVars.isEmpty()) {
    			throw new IllegalStateException("Do not put empty sets here, just remove the entry from the map");
    		}

    		Set<LLVMSimpleTerm> olderMergedRefs = new LinkedHashSet<>();
    		olderStateVars.forEach(v -> olderMergedRefs.addAll(olderToGenRefMap.getOrDefault(v, Collections.emptySet())));


    		Set<LLVMSimpleTerm> newerMergedRefs = new LinkedHashSet<>();
    		newerStateVars.forEach(v -> newerMergedRefs.addAll(newertoGenRefMap.getOrDefault(v, Collections.emptySet())));

    		Set<LLVMSimpleTerm> resultSet = new LinkedHashSet<>();
    		resultSet.addAll(olderMergedRefs);
    		resultSet.retainAll(newerMergedRefs);

    		if(resultSet.size() < olderMergedRefs.size()) {
    			newResult.addCost(LLVMCost.WEAKER_RELATION, false);
    		}

    		if(resultSet.size() < newerMergedRefs.size()) {
    			newResult.addCost(LLVMCost.WEAKER_RELATION, true);
    		}

    		if(resultSet.size() > 0) {
    			Set<LLVMSymbolicVariable> toImmutable = new LinkedHashSet<>();
    			for(LLVMSimpleTerm term : resultSet) {
    				if(term instanceof LLVMSymbolicVariable) {
    					toImmutable.add((LLVMSymbolicVariable) term);
    				}
    			}

    			resultMutable.put(entryStateVar, ImmutableCreator.create(toImmutable));
    		}



    	}
    	LLVMAbstractState stateWithEntryStateVarMap = newResult
    			.getGeneralizedState().setVarToEntryStateVarsMap(ImmutableCreator.create(resultMutable));
    	newResult.setGeneralizedState(stateWithEntryStateVarMap);



    }

    /**
     * A triple (x,y,z) representing the relation x - y = z.
     * @author cryingshadow
     * @version $Id$
     */
    private static class DistancePattern extends Triple<LLVMSymbolicVariable, LLVMSymbolicVariable, BigInteger> {

        /**
         * @param x The first variable.
         * @param y The second variable.
         * @param z The constant.
         */
        public DistancePattern(LLVMSymbolicVariable x, LLVMSymbolicVariable y, BigInteger z) {
            super(x, y, z);
        }

    }

    /**
     * A triple (x,y,z) representing the memory information that at address x, we have the value z of type y.
     * @author cryingshadow
     * @version $Id$
     */
    private static class MemoryInformation extends Quadruple<LLVMSimpleTerm, LLVMType, Boolean, LLVMSimpleTerm> {

        /**
         * @param from The address.
         * @param type The type.
         * @param unsigned Is the value unsigned?
         * @param to The value.
         */
        public MemoryInformation(LLVMSimpleTerm from, LLVMType type, boolean unsigned, LLVMSimpleTerm to) {
            super(from, type, unsigned, to);
        }

    }

}
