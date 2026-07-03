package aprove.input.Programs.llvm.states;

import java.io.*;
import java.math.*;
import java.util.*;
import java.util.Map.Entry;

import org.json.*;

import aprove.*;
import aprove.input.Programs.llvm.exceptions.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.memory.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.segraph.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.input.Programs.llvm.utils.static_analysis.*;
import aprove.strategies.Abortions.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Intersector.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.IntegerReasoning.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.SMT.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Solver.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * An abstract state is the representation of every memory information.
 *
 * IMPORTANT! These states should maintain the following invariants: 1) There
 * must not be two different references which are known to be equal. An
 * implication of this invariant is that the relations never contain simple
 * equations (i.e., equations between just two references). 2) Non-constant
 * references must not have constant values. 3) No relation in a state should be
 * a tautology. To maintain these invariants, as soon as a reference is known to
 * be equal to another reference or a constant, this reference needs to be
 * replaced by the other reference or a corresponding constant reference,
 * respectively. Tautologies need to be dropped from the state.
 *
 * However, as intermediate steps, states may temporarily contain such objects.
 * They must be cleaned before the respective state becomes a node in the SE
 * graph.
 *
 * @author Janine Repke, Jera Hensel, cryingshadow
 */
public class LLVMHeuristicState extends LLVMAbstractState {

    /**
     * @param ref A reference.
     * @param valueMap The values for the references.
     * @return The value for the specified reference as AbstractBoundedInt if known. Null otherwise.
     */
    public static LLVMValue getValue(LLVMHeuristicVariable ref, Map<LLVMHeuristicVariable, LLVMValue> valueMap) {
        return
            ref.isConcrete() ?
                AbstractBoundedInt.create(((LLVMHeuristicConstRef)ref).getIntegerValue()) :
                    valueMap.get(ref);
    }

    /**
     * Completes the specified union-find structure such that the specified references and (recursively) their
     * dereferencings of equal types are equal.
     * @param heapFunction The heap function.
     * @param firstRef A reference.
     * @param secondRef Another reference.
     * @param replacements A map holding a union-find structure for equal references.
     */
    private static void computeReplacements(
        ImmutableMap<LLVMMemoryRange, LLVMMemoryInvariant> heapFunction,
        LLVMHeuristicVariable firstRef,
        LLVMHeuristicVariable secondRef,
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements
    ) {
        LLVMHeuristicState.union(replacements, firstRef, secondRef);
        Map<LLVMType, LLVMHeuristicVariable> firstTo = new LinkedHashMap<LLVMType, LLVMHeuristicVariable>();
        Map<LLVMType, LLVMHeuristicVariable> secondTo = new LinkedHashMap<LLVMType, LLVMHeuristicVariable>();
        for (Map.Entry<LLVMMemoryRange,LLVMMemoryInvariant> heapEntry : heapFunction.entrySet()) {
            LLVMMemoryRange range = heapEntry.getKey();
            if (heapEntry.getValue() instanceof LLVMSimpleMemoryInvariant) {
                if (range.getFromRef().equals(firstRef) || range.getToRef().equals(firstRef)) {
                    firstTo.put(
                        range.getType(),
                        (LLVMHeuristicVariable)((LLVMSimpleMemoryInvariant)heapEntry.getValue()).getPointedToValue()
                    );
                } else if (range.getFromRef().equals(secondRef) || range.getToRef().equals(secondRef)) {
                    secondTo.put(
                        range.getType(),
                        (LLVMHeuristicVariable)((LLVMSimpleMemoryInvariant)heapEntry.getValue()).getPointedToValue()
                    );
                }
            } else if (heapEntry.getValue() instanceof LLVMCombinedMemoryInvariant) {
                // TODO
            } else if (Globals.useAssertions) {
                // for other case, nothing needs to be done
                assert (heapEntry.getValue() instanceof LLVMIntervalMemoryInvariant) : "Unknown invariant type!";
            }
        }
        for (Map.Entry<LLVMType, LLVMHeuristicVariable> toEntry : firstTo.entrySet()) {
            LLVMHeuristicVariable value = toEntry.getValue();
            LLVMHeuristicVariable other = secondTo.get(toEntry.getKey());
            if (
                other != null
                && !LLVMHeuristicState.find(replacements, value).equals(LLVMHeuristicState.find(replacements, other))
            ) {
                LLVMHeuristicState.computeReplacements(heapFunction, value, other, replacements);
            }
        }
    }

    /**
     * Find with path compression for a union-find structure of equal references.
     * @param replacements A union-find structure for equal references.
     * @param ref Some reference.
     * @return The representative element for ref (by which it will be replaced).
     */
    private static LLVMHeuristicVariable find(
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements,
        LLVMHeuristicVariable ref
    ) {
        if (!replacements.containsKey(ref)) {
            replacements.put(ref, ref);
            return ref;
        }
        LLVMHeuristicVariable cur = ref;
        LLVMHeuristicVariable next = replacements.get(cur);
        Set<LLVMHeuristicVariable> compress = new LinkedHashSet<LLVMHeuristicVariable>();
        while (!cur.equals(next)) {
            compress.add(cur);
            cur = next;
            next = replacements.get(cur);
        }
        for (LLVMHeuristicVariable other : compress) {
            replacements.put(other, cur);
        }
        return cur;
    }

    /**
     * Union (without height balancing) for a union-find structure of equal references.
     * TODO use existing general union-find structure in Framework or add/move general code to it and call it here
     * @param replacements A union-find structure for equal references.
     * @param ref1 Some reference.
     * @param ref2 Some other reference.
     */
    private static void union(
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements,
        LLVMHeuristicVariable ref1,
        LLVMHeuristicVariable ref2
    ) {
        final LLVMHeuristicVariable found1;
        final LLVMHeuristicVariable found2;
        final boolean preferFirst;
        if (replacements.containsKey(ref1)) {
            if (replacements.containsKey(ref2)) {
                found1 = LLVMHeuristicState.find(replacements, ref1);
                found2 = LLVMHeuristicState.find(replacements, ref2);
                preferFirst = false;
            } else {
                found1 = LLVMHeuristicState.find(replacements, ref1);
                found2 = ref2;
                replacements.put(ref2, ref2);
                preferFirst = false;
            }
        } else if (replacements.containsKey(ref2)) {
            found1 = ref1;
            found2 = LLVMHeuristicState.find(replacements, ref2);
            replacements.put(ref1, ref1);
            preferFirst = true;
        } else {
            found1 = ref1;
            found2 = ref2;
            replacements.put(ref1, ref1);
            replacements.put(ref2, ref2);
            preferFirst = false;
        }
        if (found1.isConcrete() || (!found2.isConcrete() && preferFirst)) {
            replacements.put(found2, found1);
        } else {
            replacements.put(found1, found2);
        }
    }

    /**
     * @param newModule The llvm module.
     * @param newFunctionAllocations The indices of memory areas allocated within the current function's frame.
     * @param newProgPos The program position triple containing the name of the function currently in execution, the
     *                   name of the basic block currently in execution, and the number of the instruction (program
     *                   counter, 0 is first position) within this basic block.
     * @param isRefined The refinement flag.
     * @param integerState The integer knowledge.
     * @param possTrapVals The trap value dependencies.
     * @param isAbstractRecursiveFunctionStart TODO
     * @param newAllocatedByMalloc The indices of allocations which have been allocated by malloc.
     * @param entryStateVarCorrespondenceMap Map of variables in entry state to corresponding variables in this state. only non-null for functions we want to intersect
     * @param params Strategy parameters.
     * @param inputArgs TODO
     */
    protected LLVMHeuristicState(
        LLVMModule newModule,
        ImmutableTreeSet<Integer> newFunctionAllocations,
        LLVMProgramPosition newProgPos,
        boolean isRefined,
        LLVMHeuristicIntegerState integerState,
        ImmutableMap<LLVMSymbolicVariable, LLVMTrapCondition> possTrapVals,
        boolean isAbstractRecursiveFunctionStart,
        ImmutableTreeSet<Integer> newAllocatedByMalloc,
        ImmutableMap<LLVMSymbolicVariable, ImmutableSet<LLVMSymbolicVariable>> entryStateVarCorrespondenceMap,
        ImmutableMap<Integer,Boolean> allocationChangedSinceEntryState,
        LLVMParameters params
    ) {
        super(
            newModule,
            integerState.getProgramVariables(),
            newFunctionAllocations,
            newProgPos,
            integerState.getCallStack(),
            isRefined,
            integerState,
            isAbstractRecursiveFunctionStart,
            newAllocatedByMalloc,
            possTrapVals,
            params,
            entryStateVarCorrespondenceMap,
            allocationChangedSinceEntryState
        );
    }

    /**
     * If some relation between values of the same type ensures that they cannot be equal, we can also conclude that
     * pointers to these two values cannot be equal. This method does exactly that.
     * @return A new AbstractState where the found inequalities between pointers have been added and the really added
     *         inequalities.
     */
    public LLVMSymbolicEvaluationResult addPointerInequalities(Abortion aborter) {
        // combine each one with each one, yet the order does not matter
        Set<LLVMHeuristicRelation> res = new LinkedHashSet<LLVMHeuristicRelation>();
        ArrayList<Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant>> heapList =
            new ArrayList<Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant>>(this.getMemory().entrySet());
        int size = heapList.size();
        LLVMHeuristicState state = this;
        for (int i = 0; i < size; ++i) {
            Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> entry1 = heapList.get(i);
            LLVMMemoryRange access1 = entry1.getKey();
            if (!access1.isPointwise()) {
                continue;
            } //TODO infer inequalities for invariants as well?
            if (!(entry1.getValue() instanceof LLVMSimpleMemoryInvariant)) {
                continue;
            }
            LLVMHeuristicVariable to1 =
                (LLVMHeuristicVariable)((LLVMSimpleMemoryInvariant)entry1.getValue()).getPointedToValue();
            for (int j = i + 1; j < size; ++j) {
                Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> entry2 = heapList.get(j);
                if (!(entry2.getValue() instanceof LLVMSimpleMemoryInvariant)) {
                    continue;
                }
                LLVMMemoryRange access2 = entry2.getKey();
                if (!access2.isPointwise()) {
                    continue;
                } //TODO infer inequalities for invariants as well?
                LLVMHeuristicVariable to2 =
                    (LLVMHeuristicVariable)((LLVMSimpleMemoryInvariant)entry2.getValue()).getPointedToValue();
                if (access1.getType().equals(access2.getType())) {
                    final Pair<Boolean, ? extends LLVMAbstractState> check =
                        state.checkRelation(to1, IntegerRelationType.NE, to2, aborter);
                    state = (LLVMHeuristicState)check.y;
                    if (check.x) {
                        if (to1 instanceof LLVMHeuristicVarRef && to2 instanceof LLVMHeuristicVarRef) {
                            state =
                                state.addReferenceInequalities(
                                    (LLVMHeuristicVarRef)to1,
                                    (LLVMHeuristicVarRef)to2,
                                    aborter
                                );
                        }
                        if (
                            access1.getFromRef() instanceof LLVMHeuristicVarRef
                            && access2.getFromRef() instanceof LLVMHeuristicVarRef
                        ) {
                            assert (access1.getFromRef().equals(access1.getToRef()));
                            assert (access2.getFromRef().equals(access2.getToRef()));
                            state =
                                state.addReferenceInequalities(
                                    (LLVMHeuristicVarRef)access1.getFromRef(),
                                    (LLVMHeuristicVarRef)access2.getFromRef(),
                                    aborter
                                );
                        }
                        res.addAll(
                            state.getIntegerState().getStrongestRelations(
                                this.getRelationFactory().notEqualTo(access1.getFromRef(), access2.getFromRef()),
                                aborter
                            )
                        );
                    }
                }
            }
        }
        return state.addRelations(res, aborter);
    }
    
    /**
     * @param newRels The relations to add.
     */
    public LLVMHeuristicState addProgramReferenceRelation(LLVMRelation rel) {
        HashSet<LLVMRelation> rels = new LinkedHashSet<LLVMRelation>();
        rels.addAll(this.getModule().getProgramReferenceRelations());
        rels.add(rel);
        return
            new LLVMHeuristicState(
                new LLVMModule(
                    this.getModule().getAliasDefs(),
                    this.getModule().getDataLayout(),
                    this.getModule().getDebugInformation(),
                    this.getModule().getFunctions(),
                    this.getModule().getMachine(),
                    this.getModule().getTypeDefinitions(),
                    this.getModule().getVariableDefinitions(),
                    ImmutableCreator.create(rels),
                    this.getModule().getLiveVariables(),
                    this.getModule().getReturnConditions(),
                    this.getModule().getDebugUnsignedAllocas(),
                    this.getModule().getPointerSize()
                ),
                this.getAllocatedInCurrentFunctionFrameIndices(),
                this.getProgramPosition(),
                this.isRefined(),
                this.getIntegerState(),
                this.getTrapValues(),
                this.isAbstractRecursiveFunctionStart(),
                this.getAllocatedByMallocIndices(),
                null,
                this.getAllocationChangedSinceEntryStateMap(),
                this.getStrategyParamters()
            );
    }

    /**
     * @param ref1 A non-constant reference.
     * @param ref2 Another non-constant reference.
     * @return A state where the specified references are cached to be unequal and everything else as in the current
     *         state.
     */
    public LLVMHeuristicState addReferenceInequalities(
        LLVMHeuristicVarRef ref1,
        LLVMHeuristicVarRef ref2,
        Abortion aborter
    ) {
        return
            this.setIntegerState(
                this.getIntegerState().addReferenceInequalities(ref1, ref2, aborter)
            );
    }

    @Override
    public LLVMHeuristicState addRelation(LLVMRelation rel, Abortion aborter) {
        LLVMHeuristicRelation relation = this.getRelationFactory().createRelation(rel);
        LLVMHeuristicTerm lhs = relation.getLhs();
        LLVMHeuristicTerm rhs = relation.getRhs();
        if (lhs instanceof LLVMHeuristicVariable && rhs instanceof LLVMHeuristicVariable) {
            LLVMHeuristicVariable left = (LLVMHeuristicVariable)lhs;
            LLVMHeuristicVariable right = (LLVMHeuristicVariable)rhs;
            // this might be expressed as value change or lead to replacements of variables
            switch (relation.getHeuristicRelationType()) {
                case EQ:
                    if (left.isConcrete() && right.isConcrete()) {
                        if (
                            ((LLVMHeuristicConstRef)left).getIntegerValue().compareTo(
                                ((LLVMHeuristicConstRef)right).getIntegerValue()
                            ) == 0
                        ) {
                            return this;
                        }
                        throw new IllegalStateException("Tried to add contradictive relation!");
                    }
                    return this.unifySymbolicVariables(left, right).x.cleanRelations(aborter);
                case NE:
                    if (left.isZero()) {
                        return this.unequalsZero(right);
                    }
                    if (right.isZero()) {
                        return this.unequalsZero(left);
                    }
                    if (left.isConcrete() && right.isConcrete()) {
                        if (
                            ((LLVMHeuristicConstRef)left).getIntegerValue().compareTo(
                                ((LLVMHeuristicConstRef)right).getIntegerValue()
                            ) == 0
                        ) {
                            throw new IllegalStateException("Tried to add contradictive relation!");
                        }
                        return this;
                    }
                    break;
                default:
                    // LE and LT
                    final boolean strict = relation.getHeuristicRelationType() == LLVMHeuristicRelationType.LT;
                    if (left.isConcrete()) {
                        if (right.isConcrete()) {
                            BigInteger val1 = ((LLVMHeuristicConstRef)left).getIntegerValue();
                            BigInteger val2 = ((LLVMHeuristicConstRef)right).getIntegerValue();
                            if (val1.compareTo(val2) < 0 || (!strict && val1.compareTo(val2) == 0)) {
                                return this;
                            }
                            throw new IllegalStateException("Tried to add contradictive relation!");
                        }
                        LLVMValue llvmValue = this.getValue(right);
                        LLVMHeuristicState res = this;
                        if (llvmValue == null) {
                            llvmValue = AbstractInt.getUnknown(IntegerType.UNBOUND);
                            res = res.setValue(right, llvmValue);
                        }
                        AbstractInt val = llvmValue.getThisAsAbstractInt();
                        BigInteger lower = ((LLVMHeuristicConstRef)left).getIntegerValue();
                        if (strict) {
                            lower = lower.add(BigInteger.ONE);
                        }
                        if (val.getLower().compareTo(lower) < 0) {
                            return res.setValue(right, val.setLower(IntervalBound.create(lower)));
                        }
                        return res;
                    }
                    if (right.isConcrete()) {
                        LLVMValue llvmValue = this.getValue(left);
                        LLVMHeuristicState res = this;
                        if (llvmValue == null) {
                            llvmValue = AbstractInt.getUnknown(IntegerType.UNBOUND);
                            res = res.setValue(left, llvmValue);
                        }
                        AbstractInt val = llvmValue.getThisAsAbstractInt();
                        BigInteger upper = ((LLVMHeuristicConstRef)right).getIntegerValue();
                        if (strict) {
                            upper = upper.subtract(BigInteger.ONE);
                        }
                        if (val.getUpper().compareTo(upper) > 0) {
                            return this.setValue(left, val.setUpper(IntervalBound.create(upper)));
                        }
                        return this;
                    }
                    if (relation.getHeuristicRelationType().equals(LLVMHeuristicRelationType.LE)) {
                        LLVMHeuristicRelation invRel =
                            this.getRelationFactory().createRelation(LLVMHeuristicRelationType.LE, rhs, lhs);
                        if (this.getIntegerState().checkRelation(invRel, aborter).x) {
                            LLVMHeuristicRelation eqRel =
                                this.getRelationFactory().createRelation(LLVMHeuristicRelationType.EQ, lhs, rhs);
                            return (LLVMHeuristicState)super.addRelation(eqRel, aborter);
                        }
                    }
                    if (relation.getHeuristicRelationType().equals(LLVMHeuristicRelationType.LT)) {
                        LLVMHeuristicTerm rhsMinusOne =
                            this.getRelationFactory().getTermFactory().create(
                                ArithmeticOperationType.SUB,
                                rhs,
                                (LLVMHeuristicConstRef) this.getRelationFactory().getTermFactory().constant(1)
                            );
                        LLVMHeuristicRelation invRel =
                            this.getRelationFactory().createRelation(
                                LLVMHeuristicRelationType.LE,
                                rhsMinusOne,
                                lhs
                            );
                        if (this.getIntegerState().checkRelation(invRel, aborter).x) {
                            LLVMHeuristicRelation eqRel =
                                this.getRelationFactory().createRelation(
                                    LLVMHeuristicRelationType.EQ,
                                    lhs,
                                    rhsMinusOne
                                );
                            return (LLVMHeuristicState)super.addRelation(eqRel, aborter);
                        }
                    }
            }
        }
        return (LLVMHeuristicState)super.addRelation(relation, aborter);
    }

    /**
     * @return The state emerging from this state by adjusting the values to the relations known and the replacements
     *         to constants conducted during the adjustment.
     */
    public LLVMKnowledgeResult adjustValues(Abortion aborter) {
        if (this.isAdjusted()) {
            return new LLVMKnowledgeResult(this, Collections.emptyMap(), Collections.emptyMap());
        }
        LLVMHeuristicState res = this;
        boolean changed;
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> shrinking =
            new LinkedHashMap<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>>();
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements =
            new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>();
        final LLVMHeuristicRelationFactory relationFactory = this.getRelationFactory();
        final LLVMHeuristicTermFactory termFactory = relationFactory.getTermFactory();
        do {
            outer: while (true) {
                aborter.checkAbortion();
                for (LLVMHeuristicRelation rel : res.getRelations()) {
                    LLVMKnowledgeResult adjustment = res.adjustValues(rel, aborter);
                    if (!adjustment.x.equals(res)) {
                        res = adjustment.x;
                        LLVMHeuristicExpressionUtils.updateReplacements(replacements, adjustment.z);
                        LLVMHeuristicExpressionUtils.updateReplacements(
                            replacements,
                            this.updateShrinking(shrinking, adjustment.y)
                        );
                        continue outer;
                    }
                }
                for (
                    Map.Entry<LLVMHeuristicVariable, Integer> assoc : res.getAssociations().entrySet()
                ) {
                    LLVMAllocation alloc = res.getAllocations().get(assoc.getValue());
                    LLVMHeuristicVariable ref = assoc.getKey();
                    LLVMKnowledgeResult adjustment =
                        res.adjustValues(relationFactory.createRelation(IntegerRelationType.LE, alloc.x, ref), aborter);
                    if (!adjustment.x.equals(res)) {
                        res = adjustment.x;
                        LLVMHeuristicExpressionUtils.updateReplacements(replacements, adjustment.z);
                        LLVMHeuristicExpressionUtils.updateReplacements(
                            replacements,
                            this.updateShrinking(shrinking, adjustment.y)
                        );
                        continue outer;
                    }
                    adjustment =
                        res.adjustValues(
                            relationFactory.createRelation(
                                IntegerRelationType.LE,
                                termFactory.operation(
                                    ArithmeticOperationType.ADD,
                                    ref,
                                    termFactory.constant(res.getAssociationOffsets().get(ref))
                                ),
                                alloc.y
                            ),
                            aborter
                        );
                    if (!adjustment.x.equals(res)) {
                        res = adjustment.x;
                        LLVMHeuristicExpressionUtils.updateReplacements(replacements, adjustment.z);
                        LLVMHeuristicExpressionUtils.updateReplacements(
                            replacements,
                            this.updateShrinking(shrinking, adjustment.y)
                        );
                        continue outer;
                    }
                }
                for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> entry : res.getMemory().entrySet()) {
                    if (!(entry.getKey() instanceof LLVMMemoryRecursiveRange) ||
                        !(entry.getValue() instanceof LLVMCombinedMemoryInvariant)) {
                        continue;
                    }
                    LLVMMemoryRecursiveRange range = (LLVMMemoryRecursiveRange) entry.getKey();
                    LLVMCombinedMemoryInvariant inv = (LLVMCombinedMemoryInvariant) entry.getValue();
                    LLVMKnowledgeResult adjustment = res.adjustValuesToStructInvariant(range, inv, aborter);
                    if (!adjustment.x.equals(res)) {
                        res = adjustment.x;
                        LLVMHeuristicExpressionUtils.updateReplacements(replacements, adjustment.z);
                        LLVMHeuristicExpressionUtils.updateReplacements(
                            replacements,
                            this.updateShrinking(shrinking, adjustment.y)
                        );
                        continue outer;
                    }
                }
                break;
            }
            changed = false;
            Set<Map.Entry<LLVMHeuristicVariable, LLVMValue>> entrySet =
                new LinkedHashSet<Map.Entry<LLVMHeuristicVariable, LLVMValue>>(
                    res.getValues().entrySet()
                );
            LLVMHeuristicState oldRes = res;
            for (Map.Entry<LLVMHeuristicVariable, LLVMValue> entry : entrySet) {
                LLVMValue val = entry.getValue();
                if (val.isIntLiteral()) {
                    res = res.replaceSymbolicVariable(entry.getKey(), termFactory.constant(val.getIntLiteralValue()));
                }
            }
            if (!oldRes.equals(res)) {
                changed = true;
            }
        } while (changed);
        return new LLVMKnowledgeResult(res.cleanRelations(aborter).setAdjusted(true), shrinking, replacements);
    }

    @Override
    public LLVMHeuristicState allocateMemoryAndAssociatePointer(
        LLVMSymbolicVariable lower,
        LLVMSymbolicVariable upper,
        LLVMSymbolicVariable pointer,
        LLVMPointerType type,
        boolean withinFunctionFrame,
        Set<LLVMRelation> newRels,
        Abortion aborter
    ) {
        if (Globals.useAssertions) {
            for (Map.Entry<LLVMHeuristicVariable, Integer> entry : this.getAssociations().entrySet()) {
                LLVMHeuristicVariable associatedRef = entry.getKey();
                assert (!associatedRef.equals(pointer)) : "Illegal association!";
                assert (!associatedRef.equals(lower)) : "Illegal allocation!";
                assert (!associatedRef.equals(upper)) : "Illegal allocation!";
            }
        }
        LLVMHeuristicState res =
            (LLVMHeuristicState)
                super.allocateMemoryAndAssociatePointer(lower, upper, pointer, type, withinFunctionFrame, newRels, aborter);
        int index = res.getAllocations().size() - 1;
        LLVMPointerType allocType = new LLVMPointerType(LLVMIntType.I8, this.getModule().getPointerSize(), null);
        return res.associateAccess(lower, allocType, index, newRels, aborter).associateAccess(upper, allocType, index, newRels, aborter);
    }

    @Override
    public LLVMHeuristicState applyArrayPatternHeuristicForAllocation(
        LLVMSymbolicVariable newVar,
        LLVMSymbolicVariable numVar,
        LLVMSymbolicVariable limitVar
    ) {
        // check whether the reference passed as argument has been multiplied by a constant
        // in that case, establish the usual information for arrays
        final LLVMHeuristicRelationFactory relationFactory = this.getRelationFactory();
        final LLVMHeuristicTermFactory termFactory = relationFactory.getTermFactory();
        LLVMHeuristicRelationSet rels = new LLVMHeuristicRelationSet(this.getRelations());
        LLVMHeuristicRelation toAdd = null;
        LLVMHeuristicRelation toRemove = null;
        LLVMHeuristicVariable sizeVar = null;
        if (numVar instanceof LLVMHeuristicVariable) {
            sizeVar = (LLVMHeuristicVariable)numVar;
        }
        for (LLVMHeuristicRelation rel : rels.getEquations()) {
            LLVMHeuristicTerm lhs = rel.getLhs();
            LLVMHeuristicTerm rhs = rel.getRhs();
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = lhs.toLinear();
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = rhs.toLinear();
            if (numVar.equals(lhsLinear.x)) {
                if (
                    lhsLinear.z.compareTo(BigInteger.ONE) != 0
                    || lhsLinear.y.compareTo(BigInteger.ZERO) != 0
                    || rhsLinear.y.compareTo(BigInteger.ZERO) != 0
                    || !(rhsLinear.x instanceof LLVMHeuristicVarRef)
                    || rhsLinear.z.compareTo(BigInteger.ONE) <= 0
                ) {
                    continue;
                }
                toAdd =
                    relationFactory.lessThanEquals(
                        termFactory.create(ArithmeticOperationType.ADD, (LLVMHeuristicVariable)newVar, rhs),
                        termFactory.create(
                            ArithmeticOperationType.ADD,
                            termFactory.one(),
                            (LLVMHeuristicVariable)limitVar
                        )
                    );
                if (rhs.getVariables(false).size() == 1) {
                    sizeVar = rhs.getVariables(false).iterator().next();
                }
                toRemove = rel;
                break;
            } else if (numVar.equals(rhsLinear.x)) {
                if (
                    rhsLinear.z.compareTo(BigInteger.ONE) != 0
                    || rhsLinear.y.compareTo(BigInteger.ZERO) != 0
                    || lhsLinear.y.compareTo(BigInteger.ZERO) != 0
                    || !(lhsLinear.x instanceof LLVMHeuristicVarRef)
                    || lhsLinear.z.compareTo(BigInteger.ONE) <= 0
                ) {
                    continue;
                }
                toAdd =
                    relationFactory.lessThanEquals(
                        termFactory.create(ArithmeticOperationType.ADD, (LLVMHeuristicVariable)newVar, lhs),
                        termFactory.create(
                            ArithmeticOperationType.ADD,
                            termFactory.one(),
                            (LLVMHeuristicVariable)limitVar
                        )
                    );
                if (lhs.getVariables(false).size() == 1) {
                    sizeVar = lhs.getVariables(false).iterator().next();
                }
                toRemove = rel;
                break;
            }
        }
        if (toAdd != null) {
            LLVMHeuristicState res = this;
            rels.remove(toRemove);
            rels.add(toAdd);
            if (sizeVar != null) {
                LLVMHeuristicRelation rel =
                    toAdd.applySubstitution((LLVMHeuristicVariable)newVar, LLVMHeuristicVarRef.startOfAllocatedArea);
                rel = rel.applySubstitution(sizeVar, LLVMHeuristicVarRef.sizeOfAllocatedArea);
                rel = rel.applySubstitution((LLVMHeuristicVariable)limitVar, LLVMHeuristicVarRef.endOfAllocatedArea);
                res = res.addProgramReferenceRelation(rel);
            }
            return res.setRelations(rels);
        }
        return this;
    }

    @Override
    public LLVMHeuristicState assign(String var, LLVMTerm value, LLVMType valueType, Set<LLVMRelation> newRels, Abortion aborter) {
        LLVMHeuristicVariable ref =
            LLVMHeuristicExpressionUtils.findReferenceForExpression(
                this.getValues(),
                new LLVMHeuristicRelationSet(this.getRelations()),
                (LLVMHeuristicTerm)value
            );
        if (ref != null) {
            if (newRels != null) {
                newRels.add(getRelationFactory().equalTo(ref, value));
            }
            return this.setProgramVariable(var, ref, valueType);
        }
        if (value instanceof LLVMHeuristicVariable) {
            if (newRels != null) {
                newRels.add(getRelationFactory().equalTo(ref, value));
            }
            return this.setProgramVariable(var, (LLVMHeuristicVariable)value, valueType);
        }
        LLVMHeuristicVariable freshVar = this.getRelationFactory().getTermFactory().freshVariable();
        LLVMHeuristicState res = this.setProgramVariable(var, freshVar, valueType);
        if (value != null) {
            LLVMRelation assignRel = this.getRelationFactory().equalTo(freshVar, value);
            res = res.addRelation(assignRel, aborter);
            if (newRels != null) {
                newRels.add(assignRel);
            }
        }
        return res;
    }

    @Override
    public LLVMHeuristicState associateAccess(LLVMSymbolicVariable pointer, LLVMPointerType type, Integer index, Set<LLVMRelation> newRels, Abortion aborter) {
        return (LLVMHeuristicState)super.associateAccess(pointer, type, index, newRels, aborter);
    }

    /**
     * Checks whether the specified relation (phi) follows from the specified relation set (Psi), i.e., whether
     * Psi |= phi holds.
     * @param set The set of relations representing Psi.
     * @param rel The relation representing phi.
     * @return True if the implication definitely holds, false if unknown or not holding.
     */
    public boolean checkImplication(LLVMHeuristicRelationSet set, LLVMHeuristicRelation rel, Abortion aborter) {
        long time = System.currentTimeMillis();
        // TODO Cache this?
        SMTExpression<SBool> stateInformationExp =
            Core.and(
                set.toSMTExp(),
                LLVMHeuristicIntegerState.integerBoundInformationToSMTExp(this.getValues()),
                Core.and(this.getIntegerState().allocationInformationToSMTExp()),
                this.getIntegerState().associationInformationToSMTExp()
            );
        SMTExpression<SBool> relExp = rel.toSMTExp();
        // Check if stateInformationExp && not(relExp). If UNSAT, we have an entailment:
        final LLVMParameters params = this.getStrategyParamters();
        final SMTSolver solver;
        switch (params.SMTsolver) {
            case SMTINTERPOLINT:
                // SMTInterpol currently does not support QF_NIA.
                solver = params.SMTsolver.smtSolverFactory.getSMTSolver(SMTLIBLogic.QF_LIA, aborter);
                break;
            default:
                solver = params.SMTsolver.smtSolverFactory.getSMTSolver(SMTLIBLogic.QF_NIA, aborter);
        }
        solver.addAssertion(Core.and(stateInformationExp, Core.not(relExp)));
        LLVMHeuristicRelationSet.formulaConstruction += System.currentTimeMillis() - time;
        ++LLVMHeuristicRelationSet.smtCalls;
        time = System.currentTimeMillis();
        boolean res = YNM.NO.equals(solver.checkSAT());
        LLVMHeuristicRelationSet.smtSolving += System.currentTimeMillis() - time;
        try {
            solver.dispose();
        } catch (IOException e) {
            // Disposing failed. There is nothing we can do about it, so we proceed as usual.
            e.printStackTrace(System.err);
        }
        return res;
    }

    /**
     * @return A state emerging from this state by dropping relations which are already implied by the remaining ones.
     */
    public LLVMHeuristicState cleanRelations(Abortion aborter) {
        if (this.isClean()) {
            return this;
        }
        LLVMHeuristicRelationSet rels = new LLVMHeuristicRelationSet();
        rels.addRelations(
            this.getIntegerState(),
            this.getRelations(),
            false,
            aborter
        );
        return this.setRelations(rels).setClean(true);
    }
    
    /**
     * @return A state emerging from this state by transforming struct invariants of length 1 into simple heap entries
     */
    public LLVMHeuristicState cleanStructInvariants(Abortion aborter){
        LLVMHeuristicState newState = this;
        LLVMRelationFactory relationFactory = this.getRelationFactory();
        LLVMTermFactory termFactory = relationFactory.getTermFactory();
        for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> pointsToInfo : this.getMemory().entrySet()) {
            if (!(pointsToInfo.getKey() instanceof LLVMMemoryRecursiveRange) || !(pointsToInfo.getValue() instanceof LLVMCombinedMemoryInvariant)) {
                continue;
            }
            LLVMMemoryRecursiveRange recRange = (LLVMMemoryRecursiveRange) pointsToInfo.getKey();
            LLVMCombinedMemoryInvariant structInv = (LLVMCombinedMemoryInvariant) pointsToInfo.getValue();
            // if length is 0, delete invariant
            if (recRange.getFromRef().equals(termFactory.zero())) {
                newState = (LLVMHeuristicState) newState.removeHeapAccesses(Collections.singleton(recRange));
                continue;
            }
            // check if length is 1 ...
            if (!this.checkRelation(recRange.getLength(), IntegerRelationType.EQ, termFactory.one(), aborter).x &&
                    (!structInv.getNext().equals(structInv.getLastRecursivePointer()) || !this.checkIfPositive(recRange.getLength(), aborter).x)) {
                continue;
            }
            // first create allocation and association
            LLVMPointerType pointerToStructType = new LLVMPointerType(recRange.getType(), newState.getModule().getPointerSize(), null);
            if (this.getAssociatedAllocationIndex(recRange, aborter).x == null) {
                BigInteger allocSizeMinusOne = BigInteger.valueOf(IntegerUtils.bitsToBytes(recRange.getType().size())).subtract(BigInteger.ONE);
                newState =
                    (LLVMHeuristicState)
                        LLVMAllocaInstruction.upperBound(
                            newState,
                            (LLVMHeuristicVariable) recRange.getFromRef(),
                            pointerToStructType,
                            allocSizeMinusOne,
                            null,
                            aborter
                        );
                LLVMSymbolicVariable limitRef = termFactory.freshVariable();
                LLVMRelation rel =
                    relationFactory.createAdditionRelation(limitRef, recRange.getFromRef(), termFactory.constant(allocSizeMinusOne));
                newState = newState.addRelation(rel, aborter);
                newState =
                    newState.allocateMemoryAndAssociatePointer(
                        (LLVMHeuristicVariable) recRange.getFromRef(),
                        limitRef,
                        (LLVMHeuristicVariable) recRange.getFromRef(),
                        pointerToStructType,
                        false,
                        Collections.singleton(rel),
                        aborter
                    );
            }
            // create memory knowledge
            for (Map.Entry<BigInteger,LLVMMemoryInvariant> entry : structInv.getInvariants().entrySet()) {
                BigInteger offset = entry.getKey();
                LLVMComplexMemoryInvariant inv = (LLVMComplexMemoryInvariant) entry.getValue();
                // add relation to KB: simpleRef = allocStart + offset
                LLVMHeuristicTerm refTerm = (LLVMHeuristicTerm) termFactory.add(recRange.getFromRef(), termFactory.constant(offset));
                LLVMHeuristicVariable simpleRef = LLVMHeuristicExpressionUtils.findReferenceForExpression(newState.getValues(), new LLVMHeuristicRelationSet(newState.getRelations()), refTerm);
                if (simpleRef == null) {
                    simpleRef = (LLVMHeuristicVariable) termFactory.freshVariable();
                }
                newState = newState.addRelation(relationFactory.equalTo(simpleRef, refTerm), aborter);
                // create PT entry
                LLVMSimpleTerm invRef;
                if (inv.getFirstValue() != null) {
                    if (inv.getLastValue() instanceof LLVMConstant) {
                        invRef = inv.getLastValue();
                    } else {
                        invRef = inv.getFirstValue();
                    }
                } else if (inv.getLastValue() != null) {
                    invRef = inv.getLastValue();
                } else {
                    invRef = this.getRelationFactory().getTermFactory().freshVariable();
                }
                newState = (LLVMHeuristicState) newState.setSimpleHeapEntry(simpleRef, inv.getType(), false, invRef, aborter);
                if (inv.getFirstValue() != null && inv.getLastValue() != null) {
                    LLVMRelation firstEqualsLast = relationFactory.equalTo(inv.getFirstValue(), inv.getLastValue());
                    newState = newState.addRelation(firstEqualsLast, aborter);
                }
            }
            newState = (LLVMHeuristicState) newState.removeHeapAccesses(Collections.singleton(recRange));
        }
        return newState;
    }

    @Override
    public LLVMHeuristicState clearKnowledge(Abortion aborter) {
        return
            new LLVMHeuristicState(
                this.getModule(),
                ImmutableCreator.create(new TreeSet<Integer>()),
                this.getProgramPosition(),
                this.isRefined(),
                new LLVMHeuristicIntegerState(this.getStrategyParamters()).setCallStack(this.getCallStack()),
                ImmutableCreator.create(Collections.emptyMap()),
                false,
                ImmutableCreator.create(new TreeSet<Integer>()),
                null,
                this.getAllocationChangedSinceEntryStateMap() == null ? null : ImmutableCreator.create(Collections.emptyMap()),
                this.getStrategyParamters()
            );
    }

    public boolean containsStructElementPointingTo(LLVMSimpleTerm ref, BigInteger pointerOffset, Abortion aborter) {
        LLVMHeuristicTermFactory termFactory = this.getRelationFactory().getTermFactory();
        LLVMHeuristicConstRef offsetRef = termFactory.constant(pointerOffset);
        for (Entry<LLVMMemoryRange, LLVMMemoryInvariant> memEntry : this.getMemory().entrySet()) {
            if (memEntry.getKey().isPointwise()) {
                // heap: refPointer -> ref
                LLVMSimpleTerm pointerRef = memEntry.getKey().getFromRef();
                if (pointerRef instanceof LLVMHeuristicVarRef) {
                    // relations: refPointer = someRef + pointerOffset
                    // TODO: check if someRef is the start of an allocation
                    for (LLVMHeuristicRelation rel : this.getRelations()) {
                        if (rel.getVariables(false).contains(pointerRef)) {
                            LLVMTerm ptrMinusOffset = termFactory.sub((LLVMHeuristicVarRef)pointerRef, offsetRef);
                            LLVMHeuristicVariable solved =
                                LLVMHeuristicExpressionUtils.findReferenceForExpression(
                                    this.getValues(),
                                    new LLVMHeuristicRelationSet(this.getRelations()),
                                    (LLVMHeuristicTerm)ptrMinusOffset
                                );
                            if (solved != null) {
                                return true;
                            }
                        }
                    }
                }
            }
        }
        return false;
    }
    
    public boolean containsStructWithNextPointer(LLVMTerm next, Abortion aborter) {
        for (LLVMMemoryInvariant combInv : this.getMemory().values()) {
            if (combInv instanceof LLVMCombinedMemoryInvariant) {
                for (Map.Entry<BigInteger,LLVMMemoryInvariant> inv : ((LLVMCombinedMemoryInvariant)combInv).getInvariants().entrySet()) {
                    if (inv.getValue() instanceof LLVMComplexMemoryInvariant) {
                        LLVMSimpleTerm firstVal = ((LLVMComplexMemoryInvariant)inv.getValue()).getFirstValue();
                        if (firstVal == null) {
                            continue;
                        }
                        if (firstVal.equals(next)) {
                            return true;
                        }
                        LLVMTermFactory termFactory = this.getRelationFactory().getTermFactory();
                        LLVMTerm firstPlusOffset = termFactory.add(firstVal, termFactory.constant(inv.getKey()));
                        if (this.checkRelation(firstPlusOffset, IntegerRelationType.EQ, next, aborter).x) {
                            return true;
                        }
                    }
                }
            }
        }
        return false;
    }
    
    public boolean containsStructWithStartPointer(LLVMTerm startRef, Abortion aborter) {
        for (Entry<LLVMMemoryRange, LLVMMemoryInvariant> entry : this.getMemory().entrySet()) {
            if (entry.getValue() instanceof LLVMCombinedMemoryInvariant && entry.getKey().getFromRef().equals(startRef)) {
                return true;
            }
        }
        return false;
    }

    /**
     * @param newRels The newly learned relations.
     * @param addedRels In not <code>null</code> further association relations will be added to this set
     * @return A state emerging from this state by adding further associations to yet unassociated memory accesses in
     *         case we can prove that these are between the allocation border references of some allocation where we
     *         just learned that its area might be bigger than known before.
     */
    public LLVMHeuristicState findFurtherAssociations(Collection<LLVMHeuristicRelation> newRels, Set<LLVMRelation> addedRels, Abortion aborter) {
        LLVMHeuristicState res = this;
        Map<LLVMHeuristicVariable, TreeSet<LLVMPointerType>> unassociatedPointerRefs =
            res.computeUnassociatedAccesses();
        if (unassociatedPointerRefs.isEmpty()) {
            return res;
        }
        ImmutableList<LLVMAllocation> allocs = res.getAllocations();
        for (LLVMHeuristicRelation rel : newRels) {
            if (!rel.isDirectedInequality()) {
                continue;
            }
            if (rel.isStrictInequality() && rel.isSimple()) {
                // rel is of type smaller < bigger
                res =
                    res.findAndAddFurtherAssociations(
                        unassociatedPointerRefs,
                        (LLVMHeuristicVariable)rel.getLhs(),
                        (LLVMHeuristicVariable)rel.getRhs(),
                        addedRels,
                        aborter
                    );
            }
            LLVMHeuristicTerm lhs = rel.getLhs();
            LLVMHeuristicTerm rhs = rel.getRhs();
            if (lhs instanceof LLVMHeuristicConstRef && rhs instanceof LLVMHeuristicVarRef) {
                // rel is of type c <(=) x
                LLVMHeuristicVariable relRef = (LLVMHeuristicVariable)rhs;
                for (LLVMHeuristicRelation knownRel : res.getRelations()) {
                    res =
                        res.checkRelForFurtherAssociations(
                            relRef,
                            knownRel.getLhs(),
                            knownRel.getRhs().toLinear(),
                            unassociatedPointerRefs,
                            allocs,
                            addedRels,
                            aborter
                        );
                    if (knownRel.isEquation()) {
                        res =
                            res.checkRelForFurtherAssociations(
                                relRef,
                                knownRel.getRhs(),
                                knownRel.getLhs().toLinear(),
                                unassociatedPointerRefs,
                                allocs,
                                addedRels,
                                aborter
                            );
                    }
                }
            } else if (lhs instanceof LLVMHeuristicVarRef && rhs instanceof LLVMHeuristicConstRef) {
                // rel is of type x <(=) c
                // this is only relevant if we have a relation encoding the address of an array element using x as index
                LLVMHeuristicVariable ref = (LLVMHeuristicVariable)lhs;
                if (!this.getValue(ref).getThisAsAbstractInt().isNonNegative()) {
                    continue;
                }
                for (LLVMHeuristicRelation knownRel : res.getRelations()) {
                    if (!knownRel.isEquation()) {
                        continue;
                    }
                    LLVMHeuristicTerm knownLhs = knownRel.getLhs();
                    LLVMHeuristicTerm knownRhs = knownRel.getRhs();
                    if (unassociatedPointerRefs.containsKey(knownLhs)) {
                        res =
                            res.checkArrayIndexForFurtherAssociation(
                                (LLVMHeuristicVariable)knownLhs,
                                ref,
                                ((LLVMHeuristicConstRef)rhs).getIntegerValue(),
                                knownRhs,
                                unassociatedPointerRefs,
                                allocs,
                                addedRels,
                                aborter
                            );
                    } else if (unassociatedPointerRefs.containsKey(knownRhs)) {
                        res =
                            res.checkArrayIndexForFurtherAssociation(
                                (LLVMHeuristicVariable)knownRhs,
                                ref,
                                ((LLVMHeuristicConstRef)rhs).getIntegerValue(),
                                knownLhs,
                                unassociatedPointerRefs,
                                allocs,
                                addedRels,
                                aborter
                            );
                    }
                }
            }
        }
        return res;
    }

    public LLVMSymbolicEvaluationResult findAndCreateStructInvariantForNext(LLVMSymbolicVariable startRef, Abortion aborter) {
        if (!(startRef instanceof LLVMHeuristicVarRef)) {
            return null;
        }
        LLVMHeuristicState newState = this;
        Set<LLVMRelation> rels = new HashSet<LLVMRelation>();
        LLVMHeuristicRelationFactory relationFactory = newState.getRelationFactory();
        LLVMHeuristicTermFactory termFactory = newState.getRelationFactory().getTermFactory();
        Pair<LLVMMemoryRecursiveRange,LLVMCombinedMemoryInvariant> heapEntryStartRef = this.findStructInvariantForStartRef(startRef);
        if (heapEntryStartRef != null) {
            LLVMHeuristicVariable next;
            LLVMMemoryRecursiveRange recRange;
            LLVMCombinedMemoryInvariant structInv;
            recRange = heapEntryStartRef.x;
            structInv = heapEntryStartRef.y;
            // case 1: pointsToInfo:   pointerRef --vl--> Inv, where next is nextRef
            // only create invariant if the length of the new invariant is at least 1 ...
            if (this.checkRelation(recRange.getLength(), IntegerRelationType.LE, termFactory.one(), aborter).x) {
                return null;
            }
            // ... and there is not any struct invariant for the next pointer yet.
            next = newState.getStructNext((LLVMHeuristicVarRef)startRef);
            if (next == null || next.isConcrete()) {
                return null;
            }
            for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> otherInfo : newState.getMemory().entrySet()) {
                if (otherInfo.getKey().getFromRef().equals(next) && (otherInfo.getKey() instanceof LLVMMemoryRecursiveRange)) {
                    return null;
                }
            }
            // startRef --vl--> Inv, where next is nextRef
            // => create entry nextRef -vl-1-> newInv
            LLVMHeuristicVariable nextNext = newState.getStructNext((LLVMHeuristicVarRef)next);
            if (nextNext == null) {
                nextNext = termFactory.freshVariable();
                LLVMValue newVal = LLVMIntType.I64.getInitializedIntValue(true, newState.getStrategyParamters().useBoundedIntegers).onlyNonNegative();
                newState = newState.setValue(nextNext, newVal);
            }
            // new length: vl-1
            LLVMTerm newLengthTerm = termFactory.sub(recRange.getLength(), termFactory.one());
            LLVMHeuristicVariable newLengthVar = null;
            if (!(newLengthTerm instanceof LLVMConstant)) {
                newLengthVar = termFactory.freshVariable();
                LLVMValue newLengthVal = LLVMIntType.I32.getInitializedIntValue(true, newState.getStrategyParamters().useBoundedIntegers);
                newState = newState.setValue(newLengthVar, newLengthVal);
                LLVMHeuristicRelation lengthRel = relationFactory.equalTo(newLengthVar, newLengthTerm);
                newState = newState.addRelation(lengthRel, aborter);
                rels.add(lengthRel);
            } else {
                newLengthVar = termFactory.constant(((LLVMConstant)newLengthTerm).getIntegerValue());
            }
            Map<BigInteger,LLVMMemoryInvariant> newInvs = new LinkedHashMap<>();
            // new other first values
            for (Map.Entry<BigInteger,LLVMMemoryInvariant> entry : structInv.getInvariants().entrySet()) {
                LLVMComplexMemoryInvariant inv = (LLVMComplexMemoryInvariant) entry.getValue();
                if (inv.getType().isPointerType() && inv.getType().getThisAsPointerType().pointsToStruct()) {
                    newInvs.put(entry.getKey(), inv.replaceReference(next, nextNext));
                } else {
                    // first check if there already is a value pointed to by structNext
                    LLVMHeuristicVariable newFirst = newState.getDereferencedAccessSimpleWithOffset(next, inv.getType(), false, entry.getKey(), aborter);
                    if (newFirst != null) {
                        newInvs.put(entry.getKey(), inv.replaceReference(inv.getFirstValue(), newFirst));
                    } else {
                        LLVMHeuristicVariable newFirstVar = termFactory.freshVariable();
                        if (inv.getChange().getLinearRate() == null || !inv.getType().isIntType() || !(inv.getFirstValue() instanceof LLVMHeuristicVarRef)) {
                            LLVMValue newFirstVal = inv.getType().getInitializedIntValue(false, newState.getStrategyParamters().useBoundedIntegers);
                            newState = newState.setValue(newFirstVar, newFirstVal);
                            LLVMHeuristicRelation firstRel = null;
                            if (inv.getChange().isAscending()) {
                                firstRel = relationFactory.lessThan(inv.getFirstValue(), newFirstVar);
                            } else if (inv.getChange().isDescending()) {
                                firstRel = relationFactory.lessThan(newFirstVar, inv.getFirstValue());
                            } else if (inv.getChange().isNonAscending()) {
                                firstRel = relationFactory.lessThanEquals(newFirstVar, inv.getFirstValue());
                            } else if (inv.getChange().isNonDescending()) {
                                firstRel = relationFactory.lessThanEquals(inv.getFirstValue(), newFirstVar);
                            }
                            if (firstRel != null) {
                                newState = newState.addRelation(firstRel, aborter);
                                rels.add(firstRel);
                            }
                            newInvs.put(entry.getKey(), inv.replaceReference(inv.getFirstValue(), newFirstVar));
                        } else {
                            // new first value: old first value + constant change
                            LLVMTerm newFirstTerm = termFactory.add(inv.getFirstValue(), termFactory.constant(inv.getChange().getLinearRate()));
                            LLVMValue newFirstVal = inv.getType().getInitializedIntValue(false, newState.getStrategyParamters().useBoundedIntegers);
                            newState = newState.setValue(newFirstVar, newFirstVal);
                            LLVMHeuristicRelation firstRel = relationFactory.equalTo(newFirstVar, newFirstTerm);
                            newState = newState.addRelation(firstRel, aborter);
                            rels.add(firstRel);
                            newInvs.put(entry.getKey(), inv.replaceReference(inv.getFirstValue(), newFirstVar));
                        }
                    }
                }
            }
            LLVMMemoryRecursiveRange newRange = new LLVMMemoryRecursiveRange(next, next, recRange.getType(), newLengthVar);
            LLVMCombinedMemoryInvariant newInv = new LLVMCombinedMemoryInvariant(newInvs);
            // new heap entry: nextRef -vl-1-> newInv
            LLVMPointerType pointerToStructType = structInv.getTypeOfRecPointer();
            newState = (LLVMHeuristicState) newState.setHeapEntry(newRange, newInv);
            // remove          pointerRef --vl--> Inv
            newState = (LLVMHeuristicState) newState.removeHeapAccesses(Collections.singleton(recRange));
            // recreate PT info from first entry in old struct invariant
            // first create allocation and association
            if (newState.getAssociatedAllocationIndex(recRange, aborter).x == null) {
                BigInteger allocSizeMinusOne = BigInteger.valueOf(IntegerUtils.bitsToBytes(recRange.getType().size())).subtract(BigInteger.ONE);
                newState =
                    (LLVMHeuristicState)
                        LLVMAllocaInstruction.upperBound(
                            newState,
                            (LLVMHeuristicVariable) recRange.getFromRef(),
                            pointerToStructType,
                            allocSizeMinusOne,
                            null,
                            aborter
                        );
                LLVMSymbolicVariable limitRef = termFactory.freshVariable();
                LLVMRelation rel =
                    relationFactory.createAdditionRelation(
                        limitRef,
                        recRange.getFromRef(),
                        termFactory.constant(allocSizeMinusOne)
                    );
                newState = newState.addRelation(rel, aborter);
                rels.add(rel);
                newState =
                    newState.allocateMemoryAndAssociatePointer(
                        (LLVMHeuristicVariable) recRange.getFromRef(),
                        limitRef,
                        (LLVMHeuristicVariable) recRange.getFromRef(),
                        pointerToStructType,
                        false,
                        rels,
                        aborter
                    );
            }
            // create memory knowledge
            for (Map.Entry<BigInteger,LLVMMemoryInvariant> entry : structInv.getInvariants().entrySet()) {
                BigInteger offset = entry.getKey();
                LLVMComplexMemoryInvariant inv = (LLVMComplexMemoryInvariant) entry.getValue();
                // if not present, add relation to KB: simpleRef = allocStart + offset
                LLVMHeuristicTerm refTerm =
                    relationFactory.getTermFactory().add(
                        recRange.getFromRef(),
                        termFactory.constant(offset)
                    );
                LLVMHeuristicVariable simpleRef = LLVMHeuristicExpressionUtils.findReferenceForExpression(newState.getValues(), new LLVMHeuristicRelationSet(newState.getRelations()), refTerm);
                if (simpleRef == null) {
                    simpleRef = termFactory.freshVariable();
                    LLVMRelation rel = relationFactory.equalTo(simpleRef, refTerm);
                    newState = newState.addRelation(rel, aborter);
                    rels.add(rel);
                }
                // create PT entry
                LLVMSimpleTerm invRef;
                if (inv.getFirstValue() != null) {
                    invRef = inv.getFirstValue();
                } else {
                    invRef = termFactory.freshVariable();
                }
                newState = (LLVMHeuristicState) newState.setSimpleHeapEntry(simpleRef, inv.getType(), false, invRef, aborter);
            }
        }
        if (!newState.equals(this)) {
            newState = newState.cleanStructInvariants(aborter);
        }
        return new LLVMSymbolicEvaluationResult(newState, rels);
    }

    public LLVMSymbolicEvaluationResult findAndCreateStructInvariantForNext(LLVMMemoryRange storeAccess, LLVMSymbolicVariable freshPointer, Abortion aborter) {
        LLVMHeuristicState newState = this;
        Set<LLVMRelation> rels = new HashSet<LLVMRelation>();
        LLVMHeuristicRelationFactory relationFactory = newState.getRelationFactory();
        LLVMHeuristicTermFactory termFactory = newState.getRelationFactory().getTermFactory();
        LLVMHeuristicVarRef pointerRef = (LLVMHeuristicVarRef) storeAccess.getFromRef();
        Pair<LLVMMemoryRecursiveRange,LLVMCombinedMemoryInvariant> heapEntryStartRef = this.findStructInvariantForStartRef(pointerRef);
        Pair<LLVMMemoryRecursiveRange,LLVMCombinedMemoryInvariant> heapEntryNextRef = this.findStructInvariantForNextRef(pointerRef);
        if (heapEntryStartRef != null || heapEntryNextRef != null) {
            LLVMHeuristicVariable next;
            LLVMMemoryRecursiveRange recRange;
            LLVMCombinedMemoryInvariant structInv;
            if (heapEntryStartRef != null) {
                recRange = heapEntryStartRef.x;
                structInv = heapEntryStartRef.y;
                // case 1: pointsToInfo:   pointerRef --vl--> Inv, where next is nextRef
                // only create invariant if the length of the new invariant is at least 1 ...
                if (this.checkRelation(recRange.getLength(), IntegerRelationType.LE, termFactory.one(), aborter).x) {
                    return null;
                }
                LLVMCallGraph callGraph = new LLVMCallGraph(this.getModule());
                boolean isRecFct = callGraph.getRecursiveFunctions().contains(this.getCurrentFunction());
                if (!isRecFct && !this.checkRelation(recRange.getLength(), IntegerRelationType.GE, termFactory.two(), aborter).x) {
                    if (recRange.getFromRef().equals(structInv.getLastRecursivePointer())) {
                        return findAndCreateStructInvariantForNextCyclic(recRange, structInv, freshPointer, aborter);
                    }
                    return null;
                }
                // ... and there is not any struct invariant for the next pointer yet.
                next = newState.getStructNext(pointerRef);
                if (next == null || next.isConcrete()) {
                    return null;
                }
                for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> otherInfo : newState.getMemory().entrySet()) {
                    if (otherInfo.getKey().getFromRef().equals(next) && (otherInfo.getKey() instanceof LLVMMemoryRecursiveRange)) {
                        return null;
                    }
                }
            } else {
                recRange = heapEntryNextRef.x;
                structInv = heapEntryNextRef.y;
                // case 2: pointsToInfo:   startRef --vl--> Inv, where next is pointerRef
                // only create invariant if the length of the new invariant is at least 1 ...
                if (!this.checkRelation(recRange.getLength(), IntegerRelationType.GE, termFactory.constant(2), aborter).x) {
                    return null;
                }
                // ... and there is not any struct invariant for the next pointer yet.
                next = pointerRef;
                if (next == null || next.isConcrete()) {
                    return null;
                }
                for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> otherInfo : newState.getMemory().entrySet()) {
                    if (otherInfo.getKey().getFromRef().equals(next) && (otherInfo.getKey() instanceof LLVMMemoryRecursiveRange)) {
                        return null;
                    }
                }
            }
            // case 1: pointsToInfo:   pointerRef --vl--> Inv, where next is nextRef
            //         => create entry nextRef -vl-1-> newInv
            // case 2: pointsToInfo:   startRef --vl--> Inv (where next is pointerRef)
            //         => create entry pointerRef -vl-1-> newInv
            LLVMHeuristicVariable nextNext = newState.getStructNext((LLVMHeuristicVarRef)next);
            if (nextNext == null) {
                nextNext = termFactory.freshVariable();
                LLVMValue newVal = LLVMIntType.I64.getInitializedIntValue(true, newState.getStrategyParamters().useBoundedIntegers).onlyNonNegative();
                newState = newState.setValue(nextNext, newVal);
            }
            // new length: vl-1
            LLVMTerm newLengthTerm = termFactory.sub(recRange.getLength(), termFactory.one());
            LLVMHeuristicVariable newLengthVar = null;
            if (!(newLengthTerm instanceof LLVMConstant)) {
                newLengthVar = termFactory.freshVariable();
                LLVMValue newLengthVal = LLVMIntType.I32.getInitializedIntValue(true, newState.getStrategyParamters().useBoundedIntegers);
                newState = newState.setValue(newLengthVar, newLengthVal);
                LLVMHeuristicRelation lengthRel = relationFactory.equalTo(newLengthVar, newLengthTerm);
                newState = newState.addRelation(lengthRel, aborter);
                rels.add(lengthRel);
            } else {
                newLengthVar = termFactory.constant(((LLVMConstant)newLengthTerm).getIntegerValue());
            }
            Map<BigInteger,LLVMMemoryInvariant> newInvs = new LinkedHashMap<>();
            // new other first values
            for (Map.Entry<BigInteger,LLVMMemoryInvariant> entry : structInv.getInvariants().entrySet()) {
                LLVMComplexMemoryInvariant inv = (LLVMComplexMemoryInvariant) entry.getValue();
                if (inv.getType().isPointerType() && inv.getType().getThisAsPointerType().pointsToStruct()) {
                    newInvs.put(entry.getKey(), inv.replaceReference(next, nextNext));
                } else {
                    // first check if there already is a value pointed to by structNext
                    LLVMHeuristicVariable newFirst = newState.getDereferencedAccessSimpleWithOffset(next, inv.getType(), false, entry.getKey(), aborter);
                    if (newFirst != null) {
                        newInvs.put(entry.getKey(), inv.replaceReference(inv.getFirstValue(), newFirst));
                    } else {
                        LLVMHeuristicVariable newFirstVar = termFactory.freshVariable();
                        if (inv.getChange().getLinearRate() == null || !inv.getType().isIntType() || !(inv.getFirstValue() instanceof LLVMHeuristicVarRef)) {
                            LLVMValue newFirstVal = inv.getType().getInitializedIntValue(false, newState.getStrategyParamters().useBoundedIntegers);
                            newState = newState.setValue(newFirstVar, newFirstVal);
                            LLVMHeuristicRelation firstRel = null;
                            if (inv.getChange().isAscending()) {
                                firstRel = relationFactory.lessThan(inv.getFirstValue(), newFirstVar);
                            } else if (inv.getChange().isDescending()) {
                                firstRel = relationFactory.lessThan(newFirstVar, inv.getFirstValue());
                            } else if (inv.getChange().isNonAscending()) {
                                firstRel = relationFactory.lessThanEquals(newFirstVar, inv.getFirstValue());
                            } else if (inv.getChange().isNonDescending()) {
                                firstRel = relationFactory.lessThanEquals(inv.getFirstValue(), newFirstVar);
                            }
                            if (firstRel != null) {
                                newState = newState.addRelation(firstRel, aborter);
                                rels.add(firstRel);
                            }
                            if (firstRel != null) {
                                newState = newState.addRelation(firstRel, aborter);
                                rels.add(firstRel);
                            }
                            newInvs.put(entry.getKey(), inv.replaceReference(inv.getFirstValue(), newFirstVar));
                        } else {
                            // new first value: old first value + constant change
                            LLVMTerm newFirstTerm = termFactory.add(inv.getFirstValue(), termFactory.constant(inv.getChange().getLinearRate()));
                            LLVMValue newFirstVal = inv.getType().getInitializedIntValue(false, newState.getStrategyParamters().useBoundedIntegers);
                            newState = newState.setValue(newFirstVar, newFirstVal);
                            LLVMHeuristicRelation firstRel = relationFactory.equalTo(newFirstVar, newFirstTerm);
                            newState = newState.addRelation(firstRel, aborter);
                            rels.add(firstRel);
                            newInvs.put(entry.getKey(), inv.replaceReference(inv.getFirstValue(), newFirstVar));
                        }
                    }
                }
            }
            LLVMMemoryRecursiveRange newRange = new LLVMMemoryRecursiveRange(next, next, recRange.getType(), newLengthVar);
            LLVMCombinedMemoryInvariant newInv = new LLVMCombinedMemoryInvariant(newInvs);
            // new heap entry: nextRef -vl-1-> newInv or pointerRef -vl-1-> newInv
            LLVMPointerType pointerToStructType = structInv.getTypeOfRecPointer();
            newState = (LLVMHeuristicState) newState.setHeapEntry(newRange, newInv);
            if (newState.getAssociatedAllocationIndex(storeAccess, aborter).x == null && !storeAccess.getFromRef().equals(newRange.getFromRef())) {
                BigInteger offset = BigInteger.valueOf(IntegerUtils.bitsToBytes(newRange.getType().size())).subtract(BigInteger.ONE);
                newState =
                    (LLVMHeuristicState)
                        LLVMAllocaInstruction.upperBound(
                            newState,
                            (LLVMHeuristicVariable) storeAccess.getFromRef(),
                            pointerToStructType,
                            offset,
                            rels,
                            aborter
                        );
                LLVMSymbolicVariable limitRef = termFactory.freshVariable();
                LLVMRelation rel =
                    relationFactory.createAdditionRelation(
                        limitRef,
                        storeAccess.getFromRef(),
                        termFactory.constant(offset)
                    );
                newState = newState.addRelation(rel, aborter);
                rels.add(rel);
                newState =
                        newState.allocateMemoryAndAssociatePointer(
                        (LLVMHeuristicVariable) storeAccess.getFromRef(),
                        limitRef,
                        (LLVMHeuristicVariable) storeAccess.getFromRef(),
                        pointerToStructType,
                        false,
                        rels,
                        aborter
                    );
            }
            // case 1: pointsToInfo:   pointerRef --vl--> Inv (where next is nextRef)
            //         new heap entry: nextRef -vl-1-> newInv
            //         remove          pointerRef --vl--> Inv
            // case 2: pointsToInfo:   startRef --vl--> Inv (where next is pointerRef)
            //         new heap entry: pointerRef -vl-1-> newInv
            //         remove          startRef --vl--> Inv
            newState = (LLVMHeuristicState) newState.removeHeapAccesses(Collections.singleton(recRange));
            // case 1: set             vNew -> nextRef
            // case 2: set             vNew -> Inv-next
            LLVMMemoryInvariant resInv = new LLVMSimpleMemoryInvariant(next);
            if (!recRange.getFromRef().equals(pointerRef)) {
                resInv = new LLVMSimpleMemoryInvariant(nextNext);
            }
            newState =
                (LLVMHeuristicState)
                newState.setHeapEntry(
                    new LLVMMemoryRange(freshPointer, freshPointer, pointerToStructType, storeAccess.getUnsigned()),
                    resInv
                );
            // if there is a struct invariant that ends in the old invariant, extend it to the new invariant
            boolean splitList = false;
            LLVMMemoryRecursiveRange otherRecRange = null;
            LLVMCombinedMemoryInvariant otherCombinedInv = null;
            for (Entry<LLVMMemoryRange, LLVMMemoryInvariant> otherEntry : newState.getMemory().entrySet()) {
                if (!(otherEntry.getKey() instanceof LLVMMemoryRecursiveRange) || !(otherEntry.getValue() instanceof LLVMCombinedMemoryInvariant)) {
                    continue;
                }
                // increment length
                LLVMSimpleTerm otherOldLength = ((LLVMMemoryRecursiveRange)otherEntry.getKey()).getLength();
                LLVMTerm newOtherLengthTerm = termFactory.add(otherOldLength, termFactory.one());
                LLVMHeuristicVariable newOtherLengthVar = null;
                if (!(newOtherLengthTerm instanceof LLVMConstant)) {
                    newOtherLengthVar = termFactory.freshVariable();
                    LLVMValue newOtherLengthVal = LLVMIntType.I32.getInitializedIntValue(true, newState.getStrategyParamters().useBoundedIntegers);
                    newState = newState.setValue(newOtherLengthVar, newOtherLengthVal);
                    LLVMHeuristicRelation lengthOtherRel = relationFactory.equalTo(newOtherLengthVar, newOtherLengthTerm);
                    newState = newState.addRelation(lengthOtherRel, aborter);
                    rels.add(lengthOtherRel);
                } else {
                    newOtherLengthVar = termFactory.constant(((LLVMConstant)newOtherLengthTerm).getIntegerValue());
                }
                // initialize recursive range
                otherRecRange = ((LLVMMemoryRecursiveRange) otherEntry.getKey()).setLength(newOtherLengthVar);
                otherCombinedInv = (LLVMCombinedMemoryInvariant) otherEntry.getValue();
                if (recRange.getFromRef().equals(otherCombinedInv.getLastRecursivePointer())) {
                    splitList = true;
                    break;
                }
            }
            Map<BigInteger,LLVMMemoryInvariant> otherNewInvs = new LinkedHashMap<>();
            if (splitList) {
                // extend otherInv (which corresponds to the first part of a split list)
                for (Map.Entry<BigInteger,LLVMMemoryInvariant> otherInv : otherCombinedInv.getInvariants().entrySet()) {
                    LLVMComplexMemoryInvariant otherInvValue = (LLVMComplexMemoryInvariant) otherInv.getValue();
                    LLVMSimpleTerm otherNewFirst = otherInvValue.getFirstValue();
                    LLVMSimpleTerm otherNewLast = structInv.getValue(otherInv.getKey(), otherInvValue.getType());
                    LLVMAdditiveChange change = new LLVMAdditiveChange(null);
                    if (structInv.getChange(otherInv.getKey()).getLinearRate() != null && structInv.getChange(otherInv.getKey()).getLinearRate().equals(otherInvValue.getChange().getLinearRate())) {
                        // check if "otherLast + change = structFirst" holds
                        if (otherNewLast instanceof LLVMSymbolicVariable) {
                            LLVMRelation changeRel =
                                relationFactory.createAdditionRelation(
                                    (LLVMSymbolicVariable)otherNewLast,
                                    otherInvValue.getLastValue(),
                                    termFactory.constant(otherInvValue.getChange().getLinearRate())
                                );
                            if(newState.checkRelation(changeRel, aborter).x) {
                                change = new LLVMAdditiveChange(otherInvValue.getChange().getLinearRate());
                            }
                        }
                    } else {
                        // TODO infer information about whether the list is still sorted
                    }
                    LLVMType type = otherInvValue.getType();
                    otherNewInvs.put(otherInv.getKey(), new LLVMComplexMemoryInvariant(otherNewFirst, otherNewLast, change, type));
                }
                LLVMCombinedMemoryInvariant otherNewCombinedInv = new LLVMCombinedMemoryInvariant(otherNewInvs);
                newState = (LLVMHeuristicState) newState.removeHeapAccesses(Collections.singleton(otherRecRange));
                newState = (LLVMHeuristicState) newState.setHeapEntry(otherRecRange, otherNewCombinedInv);
            }
            // otherwise recreate PT info from first entry in old struct invariant
            // first create allocation and association
            if (!splitList) {
                if (newState.getAssociatedAllocationIndex(recRange, aborter).x == null) {
                    BigInteger allocSizeMinusOne = BigInteger.valueOf(IntegerUtils.bitsToBytes(recRange.getType().size())).subtract(BigInteger.ONE);
                    newState =
                        (LLVMHeuristicState)
                            LLVMAllocaInstruction.upperBound(
                                newState,
                                (LLVMHeuristicVariable) recRange.getFromRef(),
                                pointerToStructType,
                                allocSizeMinusOne,
                                null,
                                aborter
                            );
                    LLVMSymbolicVariable limitRef = termFactory.freshVariable();
                    LLVMRelation rel =
                        relationFactory.createAdditionRelation(
                            limitRef,
                            recRange.getFromRef(),
                            termFactory.constant(allocSizeMinusOne)
                        );
                    newState = newState.addRelation(rel, aborter);
                    rels.add(rel);
                    newState =
                        newState.allocateMemoryAndAssociatePointer(
                            (LLVMHeuristicVariable) recRange.getFromRef(),
                            limitRef,
                            (LLVMHeuristicVariable) recRange.getFromRef(),
                            pointerToStructType,
                            false,
                            rels,
                            aborter
                        );
                }
                // create memory knowledge
                for (Map.Entry<BigInteger,LLVMMemoryInvariant> entry : structInv.getInvariants().entrySet()) {
                    BigInteger offset = entry.getKey();
                    LLVMComplexMemoryInvariant inv = (LLVMComplexMemoryInvariant) entry.getValue();
                    // if not present, add relation to KB: simpleRef = allocStart + offset
                    LLVMHeuristicTerm refTerm =
                        relationFactory.getTermFactory().add(
                            recRange.getFromRef(),
                            termFactory.constant(offset)
                        );
                    LLVMHeuristicVariable simpleRef = LLVMHeuristicExpressionUtils.findReferenceForExpression(newState.getValues(), new LLVMHeuristicRelationSet(newState.getRelations()), refTerm);
                    if (simpleRef == null) {
                        simpleRef = termFactory.freshVariable();
                        LLVMRelation rel = relationFactory.equalTo(simpleRef, refTerm);
                        newState = newState.addRelation(rel, aborter);
                        rels.add(rel);
                    }
                    // create PT entry
                    LLVMSimpleTerm invRef;
                    if (inv.getFirstValue() != null) {
                        invRef = inv.getFirstValue();
                    } else {
                        invRef = termFactory.freshVariable();
                    }
                    newState = (LLVMHeuristicState) newState.setSimpleHeapEntry(simpleRef, inv.getType(), false, invRef, aborter);
                }
            }
        }
        if (!newState.equals(this)) {
            newState = newState.cleanStructInvariants(aborter);
        }
        return new LLVMSymbolicEvaluationResult(newState, rels);
    }

    public LLVMSymbolicEvaluationResult findAndCreateStructInvariantForNextCyclic(LLVMMemoryRecursiveRange recRange, LLVMCombinedMemoryInvariant structInv, LLVMSymbolicVariable freshPointer, Abortion aborter) {
        LLVMHeuristicVarRef pointerRef = (LLVMHeuristicVarRef) recRange.getFromRef();
        assert (pointerRef.equals(structInv.getLastRecursivePointer()));
        LLVMHeuristicState newState = this;
        Set<LLVMRelation> rels = new HashSet<LLVMRelation>();
        LLVMHeuristicRelationFactory relationFactory = newState.getRelationFactory();
        LLVMHeuristicTermFactory termFactory = newState.getRelationFactory().getTermFactory();
        // Only search for invariant if there is not any struct invariant for the next pointer yet.
        LLVMHeuristicVariable next = newState.getStructNext(pointerRef);
        if (next == null || next.isConcrete()) {
            return null;
        }
        for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> otherInfo : newState.getMemory().entrySet()) {
            if (otherInfo.getKey().getFromRef().equals(next) && (otherInfo.getKey() instanceof LLVMMemoryRecursiveRange)) {
                return null;
            }
        }
        LLVMHeuristicVariable nextNext = newState.getStructNext((LLVMHeuristicVarRef)next);
        if (nextNext == null) {
            nextNext = termFactory.freshVariable();
            LLVMValue newVal = LLVMIntType.I64.getInitializedIntValue(true, newState.getStrategyParamters().useBoundedIntegers).onlyNonNegative();
            newState = newState.setValue(nextNext, newVal);
        }
        Map<BigInteger,LLVMMemoryInvariant> newInvs = new LinkedHashMap<>();
        // new other first values
        for (Map.Entry<BigInteger,LLVMMemoryInvariant> entry : structInv.getInvariants().entrySet()) {
            LLVMComplexMemoryInvariant inv = (LLVMComplexMemoryInvariant) entry.getValue();
            LLVMSimpleTerm newLast = inv.getFirstValue();
            if (inv.getType().isPointerType() && inv.getType().getThisAsPointerType().pointsToStruct()) {
                newInvs.put(entry.getKey(), new LLVMComplexMemoryInvariant(nextNext, newLast, new LLVMAdditiveChange(null), inv.getType()));
            } else {
                // first check if there already is a value pointed to by structNext
                LLVMHeuristicVariable newFirst = newState.getDereferencedAccessSimpleWithOffset(next, inv.getType(), false, entry.getKey(), aborter);
                if (newFirst == null) {
                    newFirst = termFactory.freshVariable();
                    if (inv.getChange().getLinearRate() == null || !inv.getType().isIntType() || !(inv.getFirstValue() instanceof LLVMHeuristicVarRef)) {
                        LLVMValue newFirstVal = inv.getType().getInitializedIntValue(false, newState.getStrategyParamters().useBoundedIntegers);
                        newState = newState.setValue(newFirst, newFirstVal);
                        LLVMHeuristicRelation firstRel = null;
                        if (inv.getChange().isAscending()) {
                            firstRel = relationFactory.lessThan(inv.getFirstValue(), newFirst);
                        } else if (inv.getChange().isDescending()) {
                            firstRel = relationFactory.lessThan(newFirst, inv.getFirstValue());
                        } else if (inv.getChange().isNonAscending()) {
                            firstRel = relationFactory.lessThanEquals(newFirst, inv.getFirstValue());
                        } else if (inv.getChange().isNonDescending()) {
                            firstRel = relationFactory.lessThanEquals(inv.getFirstValue(), newFirst);
                        }
                        if (firstRel != null) {
                            newState = newState.addRelation(firstRel, aborter);
                            rels.add(firstRel);
                        }
                    } else {
                        // new first value: old first value + constant change
                        LLVMTerm newFirstTerm = termFactory.add(inv.getFirstValue(), termFactory.constant(inv.getChange().getLinearRate()));
                        LLVMValue newFirstVal = inv.getType().getInitializedIntValue(false, newState.getStrategyParamters().useBoundedIntegers);
                        newState = newState.setValue(newFirst, newFirstVal);
                        LLVMHeuristicRelation firstRel = relationFactory.equalTo(newFirst, newFirstTerm);
                        newState = newState.addRelation(firstRel, aborter);
                        rels.add(firstRel);
                    }
                }
                // destroy linear change (should not make much of a difference for cyclic lists)
                newInvs.put(entry.getKey(), new LLVMComplexMemoryInvariant(newFirst, newLast, new LLVMAdditiveChange(null), inv.getType()));
            }
        }
        // new length = old length (cyclic list traversal)
        LLVMMemoryRecursiveRange newRange = new LLVMMemoryRecursiveRange(next, next, recRange.getType(), recRange.getLength());
        LLVMCombinedMemoryInvariant newInv = new LLVMCombinedMemoryInvariant(newInvs);
        // new heap entry: nextRef -vl-> newInv
        newState = (LLVMHeuristicState) newState.setHeapEntry(newRange, newInv);
        if (!newState.equals(this)) {
            newState = newState.cleanStructInvariants(aborter);
        }
        return new LLVMSymbolicEvaluationResult(newState, rels);
    }

    public LLVMSymbolicEvaluationResult findAndCreateStructInvariants(LLVMMemoryRange storeAccess, Abortion aborter) {
        LLVMHeuristicState res = this;
        Set<LLVMRelation> rels = new HashSet<LLVMRelation>();
        if (res.getAssociatedAllocationIndex(storeAccess, aborter).x == null) {
            return new LLVMSymbolicEvaluationResult(res, rels);
        }
        int alloc = res.getAssociatedAllocationIndex(storeAccess, aborter).x.x;
        if (!(res.getAllocations().get(alloc).x instanceof LLVMHeuristicVarRef)) {
            return new LLVMSymbolicEvaluationResult(res, rels);
        }
        LLVMHeuristicVarRef pointerRef = (LLVMHeuristicVarRef) res.getAllocations().get(alloc).x;
        for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> pointsToInfo : res.getMemory().entrySet()) {
            LLVMMemoryRange range = pointsToInfo.getKey();
            if (!range.isPointwise() || !(range.getFromRef().equals(pointerRef))) {
                continue;
            }
            if (!(pointsToInfo.getValue() instanceof LLVMSimpleMemoryInvariant)) {
                continue;
            }
            if (!(range.getFromRef() instanceof LLVMHeuristicVariable)) {
                continue;
            }
            // make it bigger
            LLVMHeuristicVariable next = res.getStructNext(pointerRef);
            if (next != null) {
                // add next to inv
                // remove next-ptr and value-ptr in memory
                for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> structInfo : res.getMemory().entrySet()) {
                    LLVMMemoryRange structRange = structInfo.getKey();
                    LLVMMemoryInvariant structInv = structInfo.getValue();
                    if (!(structRange instanceof LLVMMemoryRecursiveRange) || !(structInv instanceof LLVMCombinedMemoryInvariant)) {
                        continue;
                    }
                    if (!structRange.isPointwise()) {
                        continue;
                    }
                    if (pointerRef.equals(((LLVMCombinedMemoryInvariant)structInv).getLastRecursivePointer())) {
                        // a) make it bigger: tail extension
                        // pointsToInfo:   v82 -------> (v80,v106) (where storeAccess points to one of the fields and all fields are initialized)
                        // structInfo:     v79 --v80--> (off_j:v105..v82;?)
                        // pointerRef:     v82 (start of alloc)
                        // => create entry v79 -v80+1-> newInv
                        Set<Triple<BigInteger, LLVMType, LLVMMemoryInvariant>> structFields = this.getStructFields(pointerRef);
                        // are all fields initialized?
                        if (((LLVMMemoryRecursiveRange)structRange).getElemTypes().size() != structFields.size()) {
                            continue;
                        }
                        LLVMSimpleTerm oldLength = ((LLVMMemoryRecursiveRange)structRange).getLength();
                        LLVMHeuristicVariable newLength = res.getRelationFactory().getTermFactory().freshVariable();
                        LLVMValue length = LLVMIntType.I32.getInitializedIntValue(true, res.getStrategyParamters().useBoundedIntegers);
                        res = res.initializeValue(newLength, length);
                        LLVMHeuristicRelationFactory relFactory = res.getRelationFactory();
                        LLVMHeuristicRelation rel = relFactory.createAdditionRelation(newLength, oldLength, relFactory.getTermFactory().one());
                        res = res.addRelation(rel, aborter);
                        rels.add(rel);
                        // remove allocations contained in struct invariant
                        Set<Integer> sharedAllocs = new HashSet<>();;
                        sharedAllocs.addAll(res.getAssociatedAllocationIndices(range.getFromRef(), aborter).x);
                        while (sharedAllocs != null && !sharedAllocs.isEmpty()) {
                            res = (LLVMHeuristicState) res.removeAllocation(sharedAllocs.iterator().next(), aborter);
                            sharedAllocs = new HashSet<>();;
                            sharedAllocs.addAll(res.getAssociatedAllocationIndices(range.getFromRef(), aborter).x);
                        }
                        LLVMMemoryRecursiveRange newRange = new LLVMMemoryRecursiveRange(structRange.getFromRef(), structRange.getToRef(), structRange.getType(), newLength);
                        Map<BigInteger,LLVMMemoryInvariant> inv = new LinkedHashMap<>();
                        for (Triple<BigInteger,LLVMType,LLVMMemoryInvariant> entry : structFields) {
                            // TODO check types in case of complex invariants (if type of the corr. structInfo-inv != entry.y, return)
                            inv.put(entry.x, entry.z);
                        }
                        LLVMCombinedMemoryInvariant pointsToInv = new LLVMCombinedMemoryInvariant(inv);
                        // newInv = join((v105..v82;?),v106)
                        Pair<LLVMMemoryInvariant,? extends LLVMAbstractState> newInv =
                            structInv.joinInvariant(res, pointsToInv, aborter);
                        res = (LLVMHeuristicState) newInv.getValue();
                        res = (LLVMHeuristicState) res.removeHeapAccesses(Collections.singleton(structInfo.getKey()));
                        res = (LLVMHeuristicState) res.removeHeapAccesses(Collections.singleton(pointsToInfo.getKey()));
                        res = (LLVMHeuristicState) res.removeHeapAccesses(Collections.singleton(storeAccess));
                        res = (LLVMHeuristicState) res.setHeapEntry(newRange, newInv.getKey());
                    } else if (structRange.getFromRef().equals(next)) {
                        // b) make it bigger: front extension
                        // pointsToInfo:   v65 -------> (v49,v46)
                        // structInfo:     v46 --v64--> (v44..0;-1)
                        // => create entry v65 -v64+1-> newInv
                        LLVMSimpleTerm oldLength = ((LLVMMemoryRecursiveRange)structRange).getLength();
                        LLVMHeuristicVariable newLength = res.getRelationFactory().getTermFactory().freshVariable();
                        LLVMValue length = LLVMIntType.I32.getInitializedIntValue(true, res.getStrategyParamters().useBoundedIntegers);
                        res = res.initializeValue(newLength, length);
                        LLVMHeuristicRelationFactory relFactory = res.getRelationFactory();
                        LLVMHeuristicRelation rel = relFactory.createAdditionRelation(newLength, oldLength, relFactory.getTermFactory().one());
                        res = res.addRelation(rel, aborter);
                        rels.add(rel);
                        // remove allocations contained in struct invariant
                        Set<Integer> sharedAllocs = new HashSet<>();;
                        sharedAllocs.addAll(res.getAssociatedAllocationIndices(range.getFromRef(), aborter).x);
                        while (sharedAllocs != null && !sharedAllocs.isEmpty()) {
                            res = (LLVMHeuristicState) res.removeAllocation(sharedAllocs.iterator().next(), aborter);
                            sharedAllocs = new HashSet<>();;
                            sharedAllocs.addAll(res.getAssociatedAllocationIndices(range.getFromRef(), aborter).x);
                        }
                        LLVMMemoryRecursiveRange newRange = new LLVMMemoryRecursiveRange(pointerRef, pointerRef, structRange.getType(), newLength);
                        Map<BigInteger,LLVMMemoryInvariant> inv = new LinkedHashMap<>();
                        for (Triple<BigInteger,LLVMType,LLVMMemoryInvariant> entry : this.getStructFields(pointerRef)) {
                            // TODO check types in case of complex invariants (if type of the corr. structInfo-inv != entry.y, return)
                            inv.put(entry.x, entry.z);
                        }
                        LLVMCombinedMemoryInvariant pointsToInv = new LLVMCombinedMemoryInvariant(inv);
                        // newInv = join(v49,(v44..0;-1))
                        Pair<LLVMMemoryInvariant,? extends LLVMAbstractState> newInv =
                            pointsToInv.joinInvariant(res, structInv, aborter);
                        res = (LLVMHeuristicState) newInv.getValue();
                        res = (LLVMHeuristicState) res.setHeapEntry(newRange, newInv.getKey());
                        res = (LLVMHeuristicState) res.removeHeapAccesses(Collections.singleton(structInfo.getKey()));
                        res = (LLVMHeuristicState) res.removeHeapAccesses(Collections.singleton(pointsToInfo.getKey()));
                        res = (LLVMHeuristicState) res.removeHeapAccesses(Collections.singleton(storeAccess));
                    }
                }
                return new LLVMSymbolicEvaluationResult(res, rels);
            }
            // or c), make it smaller
            // pointsToInfo:   v329 --------> v387
            // structInfo:     v266 --v284--> (0:v264..0;-1),(8:267..0;?)
            // KB knows:       v387 is next field of v267
            // => create entry v267 -v284-1-> (0:v264-1..0;-1),(8:387..0;?)
            if (!pointsToInfo.getKey().getType().isPointerType()) {
                continue;
            }
            LLVMType targetType = ((LLVMPointerType)pointsToInfo.getKey().getType()).getTargetType();
            if (!(targetType.isStructureType()) && !(targetType instanceof LLVMNamedType)) {
                continue;
            }
            for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> structInfo : res.getMemory().entrySet()) {
                if (!(structInfo.getKey() instanceof LLVMMemoryRecursiveRange)) {
                    continue;
                }
                LLVMMemoryRecursiveRange structRange = (LLVMMemoryRecursiveRange) structInfo.getKey();
                if (!structRange.isPointwise()) {
                    continue;
                }
                LLVMCombinedMemoryInvariant structInv = (LLVMCombinedMemoryInvariant) structInfo.getValue();
                // structNext = v267
                LLVMHeuristicVariable structNext = res.getStructNext((LLVMHeuristicVarRef)structRange.getFromRef());
                if (structNext == null || structNext.isConcrete()) {
                    continue;
                }
                // structNextNext = v387
                LLVMHeuristicVariable structNextNext = res.getStructNext((LLVMHeuristicVarRef)structNext);
                if (structNextNext == null) {
                    continue;
                }
                if (!structNextNext.equals(((LLVMSimpleMemoryInvariant)pointsToInfo.getValue()).getPointedToValue())) {
                    continue;
                }
                // new length: v284-1
                LLVMHeuristicTermFactory termFactory = res.getRelationFactory().getTermFactory();
                LLVMHeuristicVariable newLengthVar = termFactory.freshVariable();
                LLVMTerm newLengthTerm = termFactory.sub(structRange.getLength(), termFactory.one());
                LLVMValue newLengthVal = LLVMIntType.I32.getInitializedIntValue(true, res.getStrategyParamters().useBoundedIntegers);
                res = res.setValue(newLengthVar, newLengthVal);
                LLVMHeuristicRelation lengthRel = res.getRelationFactory().equalTo(newLengthVar, newLengthTerm);
                res = res.addRelation(lengthRel, aborter);
                rels.add(lengthRel);
                Map<BigInteger,LLVMMemoryInvariant> newInvs = new LinkedHashMap<>();
                // new other first values
                for (Map.Entry<BigInteger,LLVMMemoryInvariant> entry : structInv.getInvariants().entrySet()) {
                    LLVMComplexMemoryInvariant inv = (LLVMComplexMemoryInvariant) entry.getValue();
                    if (inv.getType().isPointerType()) {
                        newInvs.put(entry.getKey(), inv.replaceReference(structNext, structNextNext));
                    } else {
                        // first check if there already is a value pointed to by structNext
                        LLVMHeuristicVariable newFirst = res.getDereferencedAccessSimpleWithOffset(structNext, inv.getType(), false, entry.getKey(), aborter);
                        if (newFirst != null) {
                            newInvs.put(entry.getKey(), inv.replaceReference(inv.getFirstValue(), newFirst));
                        } else {
                            LLVMHeuristicVariable newFirstVar = termFactory.freshVariable();
                            if (inv.getChange().getLinearRate() == null || !inv.getType().isIntType() || !(inv.getFirstValue() instanceof LLVMHeuristicVarRef)) {
                                newInvs.put(entry.getKey(), inv.replaceReference(inv.getFirstValue(), newFirstVar));
                                LLVMHeuristicRelation firstRel = null;
                                if (inv.getChange().isAscending()) {
                                    firstRel = res.getRelationFactory().lessThan(inv.getFirstValue(), newFirstVar);
                                } else if (inv.getChange().isDescending()) {
                                    firstRel = res.getRelationFactory().lessThan(newFirstVar, inv.getFirstValue());
                                } else if (inv.getChange().isNonAscending()) {
                                    firstRel = res.getRelationFactory().lessThanEquals(newFirstVar, inv.getFirstValue());
                                } else if (inv.getChange().isNonDescending()) {
                                    firstRel = res.getRelationFactory().lessThanEquals(inv.getFirstValue(), newFirstVar);
                                }
                                if (firstRel != null) {
                                    res = res.addRelation(firstRel, aborter);
                                    rels.add(firstRel);
                                }
                            } else {
                                // new first value: v264-1
                                LLVMTerm newFirstTerm = termFactory.add(inv.getFirstValue(), termFactory.constant(inv.getChange().getLinearRate()));
                                LLVMValue newFirstVal = inv.getType().getInitializedIntValue(false, res.getStrategyParamters().useBoundedIntegers);
                                res = res.setValue(newFirstVar, newFirstVal);
                                LLVMHeuristicRelation firstRel = res.getRelationFactory().equalTo(newFirstVar, newFirstTerm);
                                res = res.addRelation(firstRel, aborter);
                                rels.add(firstRel);
                                newInvs.put(entry.getKey(), inv.replaceReference(inv.getFirstValue(), newFirstVar));
                            }
                        }
                    }
                }
                LLVMMemoryRecursiveRange newRange = new LLVMMemoryRecursiveRange(structNext, structNext, structRange.getType(), newLengthVar);
                LLVMCombinedMemoryInvariant newInv = new LLVMCombinedMemoryInvariant(newInvs);
                res = (LLVMHeuristicState) res.setHeapEntry(newRange, newInv);
                //res = (LLVMHeuristicState) res.removeHeapAccesses(Collections.singleton(structInfo.getKey()));
                //res = (LLVMHeuristicState) res.removeHeapAccesses(Collections.singleton(pointsToInfo.getKey()));
                //res = (LLVMHeuristicState) res.removeHeapAccesses(Collections.singleton(storeAccess));
            }
        }
        return new LLVMSymbolicEvaluationResult(res, rels);
    }

    public Set<LLVMSymbolicEvaluationResult> findAndRefineStructInvariant(LLVMMemoryRange storeAccess, Abortion aborter) {
        LLVMHeuristicState newState = this;
        LLVMHeuristicRelationFactory relationFactory = newState.getRelationFactory();
        LLVMHeuristicTermFactory termFactory = newState.getRelationFactory().getTermFactory();
        LLVMHeuristicVarRef pointerRef = (LLVMHeuristicVarRef) storeAccess.getFromRef();
        Pair<LLVMMemoryRecursiveRange,LLVMCombinedMemoryInvariant> heapEntry = this.findStructInvariantForNextRef(pointerRef);
        if (heapEntry != null) {
            LLVMMemoryRecursiveRange recRange = heapEntry.x;
            if (!this.checkRelation(recRange.getLength(), IntegerRelationType.GE, termFactory.two(), aborter).x &&
                    !this.checkRelation(recRange.getLength(), IntegerRelationType.EQ, termFactory.one(), aborter).x) {
                // length may be 1 or greater => refine
                Set<LLVMSymbolicEvaluationResult> res = new LinkedHashSet<LLVMSymbolicEvaluationResult>();
                LLVMHeuristicRelation lengthEqualsOne = relationFactory.equalTo(recRange.getLength(), termFactory.one());
                LLVMHeuristicRelation lengthGreaterOrEqualsTwo = relationFactory.lessThanEquals(termFactory.two(), recRange.getLength());
                res.add(
                    new LLVMSymbolicEvaluationResult(
                        newState.addRelation(lengthEqualsOne, aborter),
                        Collections.singleton(lengthEqualsOne)
                    )
                );
                res.add(
                    new LLVMSymbolicEvaluationResult(
                        newState.addRelation(lengthGreaterOrEqualsTwo, aborter),
                        Collections.singleton(lengthGreaterOrEqualsTwo)
                    )
                );
                return res;
            }
        }
        return null;
    }

    /**
     * @param rhs The expression on the right-hand side of an equation.
     * @return A reference from this state known to equate the specified expression. Null if no such reference can be
     *         found.
     */
    public LLVMHeuristicVariable findReferenceForExpression(LLVMHeuristicTerm rhs, Abortion aborter) {
        for (LLVMHeuristicVariable ref : this.getValues().keySet()) {
            if (this.checkRelation(ref, IntegerRelationType.EQ, rhs, aborter).x) {
                return ref;
            }
        }
        return null;
    }

    public Pair<LLVMMemoryRecursiveRange,LLVMCombinedMemoryInvariant> findStructInvariantForNextRef(LLVMSymbolicVariable pointerRef) {
        LLVMHeuristicState res = this;
        for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> pointsToInfo : res.getMemory().entrySet()) {
            if (!(pointsToInfo.getKey() instanceof LLVMMemoryRecursiveRange) || !(pointsToInfo.getValue() instanceof LLVMCombinedMemoryInvariant)) {
                continue;
            }
            LLVMMemoryRecursiveRange recRange = (LLVMMemoryRecursiveRange) pointsToInfo.getKey();
            LLVMCombinedMemoryInvariant structInv = (LLVMCombinedMemoryInvariant) pointsToInfo.getValue();
            if (!(recRange.getFromRef() instanceof LLVMHeuristicVariable)) {
                continue;
            }
            // pointsToInfo:   v --l--> Inv, where next is pointerRef
            if (!(structInv.getNext().equals(pointerRef))) {
                continue;
            }
            if (!recRange.getType().isRecStructureType()) {
                continue;
            }
            return new Pair<LLVMMemoryRecursiveRange,LLVMCombinedMemoryInvariant>(recRange, structInv);
        }
        return null;
    }

    public Pair<LLVMMemoryRecursiveRange,LLVMCombinedMemoryInvariant> findStructInvariantForStartRef(LLVMSymbolicVariable pointerRef) {
        LLVMHeuristicState res = this;
        for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> pointsToInfo : res.getMemory().entrySet()) {
            if (!(pointsToInfo.getKey() instanceof LLVMMemoryRecursiveRange) || !(pointsToInfo.getValue() instanceof LLVMCombinedMemoryInvariant)) {
                continue;
            }
            LLVMMemoryRecursiveRange recRange = (LLVMMemoryRecursiveRange) pointsToInfo.getKey();
            LLVMCombinedMemoryInvariant structInv = (LLVMCombinedMemoryInvariant) pointsToInfo.getValue();
            if (!(recRange.getFromRef() instanceof LLVMHeuristicVariable)) {
                continue;
            }
            // pointerRef --l--> Inv
            if (!(recRange.getFromRef().equals(pointerRef))) {
                continue;
            }
            if (!recRange.getType().isRecStructureType()) {
                continue;
            }
            return new Pair<LLVMMemoryRecursiveRange,LLVMCombinedMemoryInvariant>(recRange, structInv);
        }
        return null;
    }

    @Override
    public LLVMHeuristicState flagAbstractRecursiveFunctionStart() {
        return
            new LLVMHeuristicState(
                this.getModule(),
                this.getAllocatedInCurrentFunctionFrameIndices(),
                this.getProgramPosition(),
                this.isRefined(),
                this.getIntegerState(),
                this.getTrapValues(),
                true,
                this.getAllocatedByMallocIndices(),
                null,
                this.getAllocationChangedSinceEntryStateMap(),
                this.getStrategyParamters()
            );
    }



    @Override
    public LLVMHeuristicState generalizeWithoutMerging() {
        return this.weakenAllocationEquations();
    }

    /**
     * @return The association offsets.
     */
    public ImmutableMap<LLVMHeuristicVariable, BigInteger> getAssociationOffsets() {
        return this.getIntegerState().getAssociationOffsets();
    }

    /**
     * @return The associations.
     */
    public ImmutableMap<LLVMHeuristicVariable, Integer> getAssociations() {
        return this.getIntegerState().getAssociations();
    }

    @Override
    public LLVMHeuristicVariable getDereferencedAccessSimple(LLVMSimpleTerm access, LLVMType targetType, boolean unsigned, Abortion aborter) {
        return (LLVMHeuristicVariable)super.getDereferencedAccessSimple(access, targetType, unsigned, aborter);
    }

    public LLVMHeuristicVariable getDereferencedAccessSimpleWithOffset(LLVMSimpleTerm access, LLVMType targetType, boolean unsigned, BigInteger offset, Abortion aborter) {
        if (offset.equals(BigInteger.ZERO)) {
            return (LLVMHeuristicVariable)super.getDereferencedAccessSimple(access, targetType, unsigned, aborter);
        }
        // TODO if there is an offset, check if access + offset = newAccess holds and call function for newAccess
        return null;
    }
    
    public LLVMMemoryRecursiveRange getMemoryRecursiveRangeWithNextPointer(LLVMSimpleTerm next) {
        for (Entry<LLVMMemoryRange, LLVMMemoryInvariant> entry : this.getMemory().entrySet()) {
            if (entry.getKey() instanceof LLVMMemoryRecursiveRange) {
                for (LLVMMemoryInvariant inv : ((LLVMCombinedMemoryInvariant)entry.getValue()).getInvariants().values()) {
                    if (inv instanceof LLVMComplexMemoryInvariant) {
                        if (((LLVMComplexMemoryInvariant)inv).getFirstValue() == null) {
                            continue;
                        }
                        if (((LLVMComplexMemoryInvariant)inv).getFirstValue().equals(next)) {
                            return (LLVMMemoryRecursiveRange) entry.getKey();
                        }
                    }
                }
            }
        }
        return null;
    }
    
    public Set<Triple<BigInteger,LLVMType,LLVMMemoryInvariant>> getStructFields(LLVMHeuristicVarRef ref) {
        Set<Triple<BigInteger,LLVMType,LLVMMemoryInvariant>> structFields = new LinkedHashSet<>();
        for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> pointsToInf : this.getMemory().entrySet()) {
            LLVMMemoryRange range = pointsToInf.getKey();
            if (!range.isPointwise() || !range.getFromRef().equals(ref) || !pointsToInf.getValue().isSimple()) {
                continue;
            }
            structFields.add(new Triple<>(BigInteger.ZERO, range.getType(), pointsToInf.getValue()));
            for (LLVMHeuristicRelation rel : this.getRelations()) {
                if (rel.getVariables(false).contains(range.getFromRef())) {
                    Pair<LLVMHeuristicTerm,Boolean> solve = rel.solveFor((LLVMHeuristicVariable)range.getFromRef());
                    if (solve == null || solve.y != null) {
                        continue;
                    }
                    LLVMHeuristicTerm solvedForFromRef = solve.x;
                    // search for all fields within this allocation
                    if (solvedForFromRef.isSumOfVariableAndConstant()) {
                        LLVMHeuristicVariable otherRef = (LLVMHeuristicVariable) solvedForFromRef.toLinear().x;
                        BigInteger offset = solvedForFromRef.toLinear().y.negate();
                        // if there is a field with negative offset, we're not at the first position
                        if (offset.compareTo(BigInteger.ZERO) < 0) {
                            continue;
                        }
                        for (Map.Entry<LLVMMemoryRange,LLVMMemoryInvariant> otherPointsToInf : this.getMemory().entrySet()) {
                            if (otherPointsToInf.getValue().isSimple() && otherPointsToInf.getKey().getFromRef().equals(otherRef)) {
                                structFields.add(
                                    new Triple<>(
                                        offset,
                                        otherPointsToInf.getKey().getType(),
                                        otherPointsToInf.getValue()
                                    )
                                );
                            }
                        }
                    }
                }
            }
        }
        if (structFields.isEmpty()) {
            return null;
        }
        // if there is only one field, we probably do not have a struct
        if (structFields.size() < 2) {
            return null;
        }
        // if there is no pointer type to a named or struct type, we do not have a (recursive) struct
        boolean containsPointerToStruct = false;
        for (Triple<BigInteger,LLVMType,LLVMMemoryInvariant> field : structFields) {
            if (field.y.isPointerType()) {
                LLVMType targetType = ((LLVMPointerType)field.y).getTargetType();
                if (targetType instanceof LLVMNamedType || targetType.isStructureType()) {
                    containsPointerToStruct = true;
                }
            }
        }
        if (!containsPointerToStruct) {
            return null;
        }
        return structFields;
    }
    
    public LLVMHeuristicVariable getStructLastPtr(Set<Triple<BigInteger,LLVMType,LLVMMemoryInvariant>> struct) {
        if (struct == null) {
            return null;
        }
        if (
            this.getStructNext(struct) == null ||
            (this.getStructNext(struct) instanceof LLVMHeuristicVarRef &&
            this.getStructNext(struct).equals(this.getStructNext((LLVMHeuristicVarRef)this.getStructNext(struct))))
        ) {
            // circular list -> length = inf
            return null;
        }
        LLVMHeuristicVariable ref = this.getStructNext(struct);
        // null check is needed to allow last pointers that are not yet initialized, e.g. for circular lists
        while (ref instanceof LLVMHeuristicVarRef && this.getStructNext((LLVMHeuristicVarRef)ref) != null) {
            if (this.isInitialStructPointer(ref)) {
                // stop here to prevent sharing
                return ref;
            } else if (this.isStructPointer(ref)) {
                // forbid sharing
                return null;
            }
            ref = this.getStructNext((LLVMHeuristicVarRef)ref);
        }
        return ref;
    }
    
    public BigInteger getStructLength(Set<Triple<BigInteger,LLVMType,LLVMMemoryInvariant>> struct, LLVMHeuristicVariable lastPtr) {
        if (struct == null || lastPtr == null) {
            return null;
        }
        if (
            this.getStructNext(struct) == null ||
            (this.getStructNext(struct) instanceof LLVMHeuristicVarRef &&
            this.getStructNext(struct).equals(this.getStructNext((LLVMHeuristicVarRef)this.getStructNext(struct))))
        ) {
            // circular list -> length = inf
            return null;
        }
        // if the next pointer is the last pointer, we have length 1
        if (this.getStructNext(struct).equals(lastPtr)) {
            return BigInteger.ONE;
        }
        BigInteger l = this.getStructLength(this.getStructFields((LLVMHeuristicVarRef)this.getStructNext(struct)), lastPtr);
        if (l != null) {
            return l.add(BigInteger.ONE);
        } else {
            return null;
        }
    }
    
    public LLVMHeuristicVariable getStructNext(LLVMHeuristicVarRef ref) {
        // if there is already a struct for ref, use it
        for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> pointsToInf : this.getMemory().entrySet()) {
            LLVMMemoryRange range = pointsToInf.getKey();
            if (!(range instanceof LLVMMemoryRecursiveRange) || !(pointsToInf.getValue() instanceof LLVMCombinedMemoryInvariant)) {
                continue;
            }
            if (!range.getFromRef().equals(ref)) {
                continue;
            }
            LLVMCombinedMemoryInvariant invs = (LLVMCombinedMemoryInvariant) pointsToInf.getValue();
            for (Map.Entry<BigInteger,LLVMMemoryInvariant> inv : invs.getInvariants().entrySet()) {
                if (!(inv.getValue() instanceof LLVMComplexMemoryInvariant)) {
                    continue;
                }
                LLVMSimpleTerm next = ((LLVMComplexMemoryInvariant)inv.getValue()).getFirstValue();
                if (!((LLVMComplexMemoryInvariant)inv.getValue()).getType().isPointerType()) {
                    continue;
                }
                if (next instanceof LLVMHeuristicVarRef) {
                    return (LLVMHeuristicVarRef) next;
                }
            }
        }
        // else, use knowledge base
        return this.getStructNext(this.getStructFields(ref));
    }
        
    public LLVMHeuristicVariable getStructNext(Set<Triple<BigInteger,LLVMType,LLVMMemoryInvariant>> struct) {
        LLVMHeuristicVariable next = null;
        if (struct == null) {
            return null;
        }
        for (Triple<BigInteger,LLVMType,LLVMMemoryInvariant> field : struct) {
            if (!field.y.isPointerType()) {
                continue;
            }
            LLVMType targetType = ((LLVMPointerType)field.y).getTargetType();
            if (!(targetType instanceof LLVMNamedType) && !(targetType.isStructureType())) {
                continue;
            }
            if (next == null) {
                if (field.z.getUsedReferences().size() == 1) {
                    next = (LLVMHeuristicVariable) field.z.getUsedReferences().iterator().next();
                } else {
                    return null;
                }
            } else {
                // we do not know which one of the struct pointers is the "next" pointer
                return null;
            }
        }
        return next;
    }
    
    public Set<Pair<BigInteger,LLVMSimpleTerm>> getStructRefs(LLVMHeuristicVarRef ref) {
        Set<Pair<BigInteger,LLVMSimpleTerm>> structRefs = new LinkedHashSet<>();
        for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> pointsToInf : this.getMemory().entrySet()) {
            LLVMMemoryRange range = pointsToInf.getKey();
            if (!range.isPointwise() || !range.getFromRef().equals(ref) || !pointsToInf.getValue().isSimple()) {
                continue;
            }
            structRefs.add(new Pair<>(BigInteger.ZERO, pointsToInf.getKey().getFromRef()));
            for (LLVMHeuristicRelation rel : this.getRelations()) {
                if (rel.getVariables(false).contains(range.getFromRef())) {
                    Pair<LLVMHeuristicTerm,Boolean> solve = rel.solveFor((LLVMHeuristicVariable)range.getFromRef());
                    if (solve == null || solve.y != null) {
                        continue;
                    }
                    LLVMHeuristicTerm solvedForFromRef = solve.x;
                    // search for all fields within this allocation
                    if (solvedForFromRef.isSumOfVariableAndConstant()) {
                        LLVMHeuristicVariable otherRef = (LLVMHeuristicVariable) solvedForFromRef.toLinear().x;
                        BigInteger offset = solvedForFromRef.toLinear().y.negate();
                        // if there is a field with negative offset, we're not at the first position
                        if (offset.compareTo(BigInteger.ZERO) < 0) {
                            continue;
                        }
                        for (Map.Entry<LLVMMemoryRange,LLVMMemoryInvariant> otherPointsToInf : this.getMemory().entrySet()) {
                            if (otherPointsToInf.getValue().isSimple() && otherPointsToInf.getKey().getFromRef().equals(otherRef)) {
                                structRefs.add(
                                    new Pair<>(
                                        offset,
                                        otherPointsToInf.getKey().getFromRef()
                                    )
                                );
                            }
                        }
                    }
                }
            }
        }
        if (structRefs.isEmpty()) {
            return null;
        }
        // if there is only one field, we probably do not have a struct
        if (structRefs.size() < 2) {
            return null;
        }
        return structRefs;
    }
    
    public List<LLVMSymbolicVariable> getStructValues(Set<Triple<BigInteger,LLVMType,LLVMMemoryInvariant>> struct, BigInteger offset, LLVMHeuristicVariable lastPtr) {
        List<LLVMSymbolicVariable> values = new LinkedList<>();
        Set<Triple<BigInteger,LLVMType,LLVMMemoryInvariant>> next = struct;
        Set<Triple<BigInteger,LLVMType,LLVMMemoryInvariant>> previous = null;
        while (
            next != null &&
            !this.getStructNext(next).equals(lastPtr) &&
            !(next.equals(previous))
        ) {
            previous = next;
            for (Triple<BigInteger,LLVMType,LLVMMemoryInvariant> triple : next) {
                if (triple.x.equals(offset)) {
                    values.add(triple.z.getUsedReferences().iterator().next());
                    break;
                }
            }
            next = this.getStructFields((LLVMHeuristicVarRef)this.getStructNext(next));
        }
        if (next != null) {
            for (Triple<BigInteger,LLVMType,LLVMMemoryInvariant> triple : next) {
                if (triple.x.equals(offset)) {
                    values.add(triple.z.getUsedReferences().iterator().next());
                    break;
                }
            }
        }
        return values;
    }
    
    public LLVMMemoryInvariant getStructWithNextPointer(LLVMTerm next) {
        for (LLVMMemoryInvariant combInv : this.getMemory().values()) {
            if (combInv instanceof LLVMCombinedMemoryInvariant) {
                for (LLVMMemoryInvariant inv : ((LLVMCombinedMemoryInvariant)combInv).getInvariants().values()) {
                    if (inv instanceof LLVMComplexMemoryInvariant) {
                        if (((LLVMComplexMemoryInvariant)inv).getFirstValue() == null) {
                            continue;
                        }
                        if (((LLVMComplexMemoryInvariant)inv).getFirstValue().equals(next)) {
                            return combInv;
                        }
                    }
                }
            }
        }
        return null;
    }

    /**
     * @return The initial heap addresses.
     */
    public ImmutableMap<Integer, LLVMHeuristicVariable> getInitialHeapAddresses() {
        return this.getIntegerState().getInitialHeapAddresses();
    }

    @Override
    public LLVMHeuristicIntegerState getIntegerState() {
        return (LLVMHeuristicIntegerState)super.getIntegerState();
    }

    /**
     * This method is only kept for testing purposes. Do not use, use getRelations() instead.
     * @return A set of relations containing knowledge holding in this state which might be useful for termination
     *         proofs. This method implements a heuristic and does not return the complete knowledge.
     */
    @Deprecated
    public IntegerRelationSet getInvariantsOld() {
        IntegerRelationSet res = new IntegerRelationSet();
        final LLVMHeuristicRelationFactory relationFactory = this.getRelationFactory();
        final LLVMHeuristicTermFactory termFactory = relationFactory.getTermFactory();
        for (Map.Entry<LLVMHeuristicVariable, LLVMValue> entry : this.getValues().entrySet()) {
            AbstractBoundedInt value = entry.getValue().getThisAsAbstractBoundedInt();
            if (value.isBiggerOne()) {
                res.add(
                    relationFactory.createRelation(
                        LLVMHeuristicRelationType.LT,
                        termFactory.one(),
                        entry.getKey()
                    )
                );
            } else if (value.isPositive()) {
                res.add(
                    relationFactory.createRelation(
                        LLVMHeuristicRelationType.LT,
                        termFactory.zero(),
                        entry.getKey()
                    )
                );
            } else if (value.isNonNegative()) {
                res.add(
                    relationFactory.createRelation(
                        LLVMHeuristicRelationType.LE,
                        termFactory.zero(),
                        entry.getKey()
                    )
                );
            } else if (value.isSmallerMinusOne()) {
                res.add(
                    relationFactory.createRelation(
                        LLVMHeuristicRelationType.LT,
                        entry.getKey(),
                        termFactory.negone()
                    )
                );
            } else if (value.isNegative()) {
                res.add(
                    relationFactory.createRelation(
                        LLVMHeuristicRelationType.LT,
                        entry.getKey(),
                        termFactory.zero()
                    )
                );
            } else if (value.isNonPositive()) {
                res.add(
                    relationFactory.createRelation(
                        LLVMHeuristicRelationType.LE,
                        entry.getKey(),
                        termFactory.zero()
                    )
                );
            }
        }
        for (LLVMHeuristicRelation rel : this.getRelations()) {
            if (rel.isDirectedInequality() || (rel.isEquation() && rel.getVariables(false).size() > 2)) {
                res.add(rel);
            }
        }
        return res;
    }

    @Override
    public LLVMHeuristicRelationFactory getRelationFactory() {
        return (LLVMHeuristicRelationFactory)super.getRelationFactory();
    }

    /**
     * @return The relations.
     */
    public ImmutableSet<LLVMHeuristicRelation> getRelations() {
        return this.getIntegerState().getRelations();
    }

    @Override
    public LLVMHeuristicVariable getSimpleTermForLiteral(LLVMLiteral lit) {
        return (LLVMHeuristicVariable)super.getSimpleTermForLiteral(lit);
    }

    @Override
    public LLVMHeuristicVariable getSymbolicVariableForProgramVariable(String varName) {
        return (LLVMHeuristicVariable)super.getSymbolicVariableForProgramVariable(varName);
    }

    /**
     * @return The cache of unequal symbolic variables.
     */
    public ImmutableSet<ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>> getUnequalCache() {
        return this.getIntegerState().getUnequalCache();
    }

    /**
     * @param heapUsed Are all heap references considered to be used?
     * @param allocationsUsed TODO
     * @return A set containing all references to which a program variable points to, which marks a border of an
     *         allocated memory area, or which occurs in the heap function (the latter only if heapUsed is true).
     */
    public Set<LLVMHeuristicVariable> getUsedReferences(boolean heapUsed, boolean allocationsUsed) {
        // all references, to which a program variable is pointing to, are used
        Set<LLVMHeuristicVariable> res = new LinkedHashSet<LLVMHeuristicVariable>();
        for (ImmutablePair<LLVMSymbolicVariable, LLVMType> pair : this.getProgramVariables().values()) {
            LLVMHeuristicVariable var = (LLVMHeuristicVariable)pair.x;
            if (!var.isConcrete()) {
                res.add(var);
            }
        }
        // all references to which program variables from other stack frames are pointing to are used
        for (LLVMReturnInformation retInfo: this.getCallStack()) {
            for (ImmutablePair<LLVMSymbolicVariable, LLVMType> pair: retInfo.getProgramVariables().values()) {
                LLVMHeuristicVariable var = (LLVMHeuristicVariable)pair.x;
                if (!var.isConcrete()) {
                    res.add(var);
                }
            }
        }
        // all references in allocated memory areas are used
        if(allocationsUsed) {
	        for (LLVMAllocation pair : this.getAllocations()) {
	            LLVMHeuristicVariable left = (LLVMHeuristicVariable)pair.x;
	            LLVMHeuristicVariable right = (LLVMHeuristicVariable)pair.y;
	            if (!left.isConcrete()) {
	                res.add(left);
	            }
	            if (!right.isConcrete()) {
	                res.add(right);
	            }
	        }
        }
        // all references in the initial heap addresses map are used
        res.addAll(this.getInitialHeapAddresses().values());
        if (heapUsed) {
            // all references in the heap function are used
            for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> entry : this.getMemory().entrySet()) {
                LLVMHeuristicVariable lower = (LLVMHeuristicVariable)entry.getKey().getFromRef();
                LLVMHeuristicVariable upper = (LLVMHeuristicVariable)entry.getKey().getToRef();
                if (!lower.isConcrete()) {
                    res.add(lower);
                }
                if (!upper.isConcrete()) {
                    res.add(upper);
                }
                if (entry.getKey() instanceof LLVMMemoryRecursiveRange) {
                    LLVMMemoryRecursiveRange recRange = (LLVMMemoryRecursiveRange) entry.getKey();
                    if (recRange.getLength() instanceof LLVMHeuristicVarRef) {
                        res.add((LLVMHeuristicVarRef)recRange.getLength());
                    }
                }
                if (entry.getValue() instanceof LLVMSimpleMemoryInvariant) {
                    LLVMHeuristicVariable to =
                        (LLVMHeuristicVariable)((LLVMSimpleMemoryInvariant)entry.getValue()).getPointedToValue();

                    if (!to.isConcrete()) {
                        res.add(to);
                    }
                }
                if (entry.getValue() instanceof LLVMCombinedMemoryInvariant) {
                    for (LLVMSymbolicVariable ref : entry.getValue().getUsedReferences()) {
                        if (ref instanceof LLVMHeuristicVarRef) {
                            res.add((LLVMHeuristicVarRef)ref);
                        }
                    }
                }
            }
            //        } else {
            //            // add all dereferenced references (transitive closure)
            //            ArrayDeque<LLVMReference> todo = new ArrayDeque<LLVMReference>(res);
            //            while (!todo.isEmpty()) {
            //                LLVMReference ref = todo.pollFirst();
            //                LLVMReference derefedRef = this.getDereferencedVariable(ref);
            //                // If this is new, also add it to todo:
            //                if (derefedRef != null && !derefedRef.isConcrete() && res.add(derefedRef)) {
            //                    todo.offerLast(derefedRef);
            //                }
            //            }
        }
        //        // add max n address (n-limited transitive closure)
        //        todo.clear();
        //        todo.addAll(res);
        //        Map<LLVMReference, Set<LLVMReference>> invertedHeap =
        //            new LinkedHashMap<LLVMReference, Set<LLVMReference>>();
        //        for (Map.Entry<LLVMReference, LLVMReference> entry : this.heap.entrySet()) {
        //            LLVMReference source = entry.getValue();
        //            Set<LLVMReference> targets = invertedHeap.get(source);
        //            if (targets == null) {
        //                targets = new LinkedHashSet<LLVMReference>();
        //                invertedHeap.put(source, targets);
        //            }
        //            targets.add(entry.getKey());
        //        }
        //        while (!todo.isEmpty()) {
        //            LLVMReference ref = todo.pollFirst();
        //            Set<LLVMReference> targets = invertedHeap.get(ref);
        //            if (targets != null) {
        //                for (LLVMReference invertedRef : targets) {
        //                    if (!invertedRef.isConcrete() && res.add(invertedRef)) {
        //                        todo.offerLast(invertedRef);
        //                    }
        //                }
        //            }
        //        }
        return res;
    }

    /**
     * @param ref The reference to be found.
     * @return The value of the reference in the value function of this state.
     */
    public LLVMValue getValue(LLVMHeuristicVariable ref) {
        return LLVMHeuristicState.getValue(ref, this.getValues());
    }

    /**
     * @return The values.
     */
    public ImmutableMap<LLVMHeuristicVariable, LLVMValue> getValues() {
        return this.getIntegerState().getValues();
    }

    @Override
    public LLVMHeuristicState initial(Abortion aborter) {
        // initial states are clean and adjusted by construction
        return this.setClean(true).setAdjusted(true);
    }

//    /**
//     * Turn the value map into a set of relations
//     * @return A RelationSet representing the state's values
//     */
//    public IntegerRelationSet getValuesAsRelations() {
//        IntegerRelationSet relations = new IntegerRelationSet();
//        for (Map.Entry<LLVMHeuristicVariable, LLVMValue> entry :
//            this.getValues().entrySet()
//        ) {
//            if (entry.getKey().isConcrete() || entry.getValue().isIntLiteral()) {
//                throw new IllegalStateException("Inconsistent values for " + entry);
//            }
//            LLVMHeuristicVarRef reference = (LLVMHeuristicVarRef)entry.getKey();
//            AbstractInt value = entry.getValue().getThisAsAbstractInt();
//            IntervalBound lower = value.getLower();
//            IntervalBound upper = value.getUpper();
//            if (lower.isFinite()) {
//                LLVMHeuristicConstRef lowerRef = this.getTermFactory().constRef(lower.getConstant());
//                relations.add(new LLVMHeuristicRelation(
//                    HeuristicRelationType.LE, lowerRef, reference
//                ));
//            }
//            if (upper.isFinite()) {
//                LLVMHeuristicConstRef upperRef = this.getTermFactory().constRef(upper.getConstant());
//                relations.add(new LLVMHeuristicRelation(
//                    HeuristicRelationType.LE, reference, upperRef
//                ));
//            }
//            if (!value.containsLiteral(0)) {
//                relations.add(new LLVMHeuristicRelation(
//                    HeuristicRelationType.NE, reference, LLVMHeuristicTermFactory.ZERO
//                ));
//            }
//        }
//        return relations;
//    }
//
//    /**
//     * TODO do we need extra information?
//     * Creates from this heap an SMT formula with link information. For each variable which is in the heap a formula is
//     * created, which describes the pointer connection between the heap variable and the pointer. E.g. if *%x and *%y
//     * is in the heap with the same type, then the formula '%x = %y => *%x = *%y' is created.
//     * @return An SMT formula with link information.
//     */
//    public Formula<SMTLIBTheoryAtom> heapToSMTExtraInformation() {
//        Formula<SMTLIBTheoryAtom> formula;
//        FormulaFactory<SMTLIBTheoryAtom> factory = new AtomCachingFactory<SMTLIBTheoryAtom>();
//        List<Formula<SMTLIBTheoryAtom>> smtList = new LinkedList<Formula<SMTLIBTheoryAtom>>();
//        Set<HeapRange> remainingHeapKeys = new LinkedHashSet<HeapRange>(this.getHeap().keySet());
//        for (HeapRange heap1 : this.getHeap().keySet()) {
//            remainingHeapKeys.remove(heap1);
//            for (HeapRange heap2 : remainingHeapKeys) {
//                assert(heap1.getFromRef() == heap1.getToRef());
//                assert(heap2.getFromRef() == heap2.getToRef());
//                if (!heap1.getType().equals(heap2.getType()) || heap1.getFromRef().equals(heap2.getFromRef())) {
//                    continue;
//                }
//                SMTLIBIntValue var1Value = heap1.getFromRef().toSMTIntValue();
//                SMTLIBIntValue var2Value = heap2.getFromRef().toSMTIntValue();
//                SMTLIBIntValue var1PointerVal = this.getDereferencedAccessSimple(heap1).toSMTIntValue();
//                SMTLIBIntValue var2PointerVal = this.getDereferencedAccessSimple(heap2).toSMTIntValue();
//                // create formula: %var1 = %var2 => *%var1 = *%var2
//                SMTLIBIntEquals eq1 = SMTLIBIntEquals.create(var1PointerVal, var2PointerVal);
//                SMTLIBIntEquals eq2 = SMTLIBIntEquals.create(var1Value, var2Value);
//                smtList.add(factory.buildImplication(factory.buildTheoryAtom(eq1), factory.buildTheoryAtom(eq2)));
//            }
//        }
//        formula = factory.buildAnd(smtList);
//        return formula;
//    }

    /**
     * @return Have the values been adjusted?
     */
    public boolean isAdjusted() {
        return this.getIntegerState().isAdjusted();
    }

    /**
     * @return Are the relations clean?
     */
    public boolean isClean() {
        return this.getIntegerState().isClean();
    }

    @Override
    public boolean isInitialStructPointer(LLVMSymbolicVariable pointerRef) {
        for (Map.Entry<LLVMMemoryRange,LLVMMemoryInvariant> entry : this.getMemory().entrySet()) {
            if (entry.getKey() instanceof LLVMMemoryRecursiveRange) {
                if (entry.getKey().getFromRef().equals(pointerRef)) {
                    return true;
                }
            }
        }
        return false;
    }

    @Override
    public boolean isStructPointer(LLVMSymbolicVariable pointerRef) {
        for (Map.Entry<LLVMMemoryRange,LLVMMemoryInvariant> entry : this.getMemory().entrySet()) {
            if (entry.getKey() instanceof LLVMMemoryRecursiveRange) {
                if (entry.getKey().getFromRef().equals(pointerRef)) {
                    return true;
                }
                if (entry.getValue().usesReference(pointerRef)) {
                    return true;
                }
                // check if there is a relation pointerRef = offset + listPtr
                for (LLVMRelation rel : this.getRelations()) {
                    if (rel.getLhs().equals(pointerRef)) {
                        if (rel.getRhs() instanceof LLVMOperation) {
                            LLVMOperation offsetPlusListPtr = (LLVMOperation) rel.getRhs();
                            if (offsetPlusListPtr.getRhs().equals(entry.getKey().getFromRef()) && offsetPlusListPtr.getLhs() instanceof LLVMConstant) {
                                LLVMConstant offset = (LLVMConstant) offsetPlusListPtr.getLhs();
                                BigInteger structSize = BigInteger.valueOf(IntegerUtils.bitsToBytes(entry.getKey().getType().size()));
                                if (offset.getIntegerValue().compareTo(BigInteger.ZERO) >= 0 && offset.getIntegerValue().compareTo(structSize) < 0) {
                                    return true;
                                }
                            }
                        }
                    }
                }
            }
        }
        return false;
    }

    /**
     * @return A state whose position and variable function are set to the top-most return information in the current
     *         call stack and a call stack like the current one without the top-most element. Moreover, all allocations
     *         known to be within the stack frame are dropped (and so are the associations to these allocations).
     *         Everything else is as in the current state.
     */
    @Override
    public LLVMHeuristicState popCallStack(Abortion aborter) {
        // since associations are only removed, there is no need to check whether we can restore trap values
        return (LLVMHeuristicState)super.popCallStack(aborter);
    }

    @Override
    public LLVMSymbolicEvaluationResult postProcessAfterRefinement(Abortion aborter, boolean removeNonLiveVariables) {
        return this.postProcess(this.setRefined(true).cleanStructInvariants(aborter).addPointerInequalities(aborter), Collections.emptySet(), false, aborter);
    }

    @Override
    public LLVMHeuristicState putTrapValue(LLVMSymbolicVariable trap, LLVMTrapCondition condition)
    throws UndefinedBehaviorException {
        return (LLVMHeuristicState)super.putTrapValue(trap, condition);
    }

    /**
     * Replace all occurrences of one symbolic variable by another. Attention: By this method we might obtain
     * tautological relations which must be cleaned thereafter.
     * @param toReplaceVar The variable to replace.
     * @param replacementVar The variable that should be used instead.
     * @return The state where the replacement has been done.
     */
    public LLVMHeuristicState replaceSymbolicVariable(
        LLVMHeuristicVariable toReplaceVar,
        LLVMHeuristicVariable replacementVar
    ) {
        Map<LLVMSymbolicVariable, LLVMTrapCondition> newTraps =
            new LinkedHashMap<LLVMSymbolicVariable, LLVMTrapCondition>();
        for (Map.Entry<LLVMSymbolicVariable, LLVMTrapCondition> entry : this.getTrapValues().entrySet()) {
            if (entry.getKey().equals(toReplaceVar)) {
                newTraps.put(replacementVar, entry.getValue().applySubstitution(toReplaceVar, replacementVar));
            } else {
                newTraps.put(entry.getKey(), entry.getValue().applySubstitution(toReplaceVar, replacementVar));
            }
        }
        LLVMIntegerState newIntegerState = this.getIntegerState().replaceSymbolicVariable(toReplaceVar, replacementVar);
        return this.setIntegerState(newIntegerState).setTrapValues(newTraps);
    }

    /**
     * Cleans up the state so that value, heap, and association mappings and the relation set only consider actually
     * used references.
     * @param old The old set of used references.
     * @return The cleaned state.
     */
    public LLVMHeuristicState restrictToUsedReferences(Set<LLVMHeuristicVariable> old, Abortion aborter) {
        if (!LLVMDebuggingFlags.USE_RESTRICTION_TO_USED_REFS) {
            return this;
        }
        if (this.isErrorState()) {
            // we have an error state which must not be restricted anymore
            return this;
        }
        Set<LLVMHeuristicVariable> usedReferences = this.getUsedReferences(true, true);
        if (old != null && usedReferences.containsAll(old)) {
            // we do not have to drop any references
            return this;
        }
        Map<LLVMHeuristicVariable, LLVMValue> newValues =
            new LinkedHashMap<LLVMHeuristicVariable, LLVMValue>(this.getValues());
        newValues.keySet().retainAll(usedReferences);
        Map<LLVMMemoryRange, LLVMMemoryInvariant> newHeap = new LinkedHashMap<LLVMMemoryRange, LLVMMemoryInvariant>(this.getMemory());
        Iterator<LLVMMemoryRange> heapIt = newHeap.keySet().iterator();
        while (heapIt.hasNext()) {
            final LLVMMemoryRange nextInv = heapIt.next();
            if (!usedReferences.contains(nextInv.getFromRef()) && !usedReferences.contains(nextInv.getToRef())) {
                heapIt.remove();
            }
        }
        Map<LLVMHeuristicVariable, Integer> newAssocs =
            new LinkedHashMap<LLVMHeuristicVariable, Integer>(this.getAssociations());
        newAssocs.keySet().retainAll(usedReferences);
        Map<LLVMHeuristicVariable, BigInteger> newAssocOffsets =
            new LinkedHashMap<LLVMHeuristicVariable, BigInteger>(this.getAssociationOffsets());
        newAssocOffsets.keySet().retainAll(usedReferences);
        Set<ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>> newUnequalCache =
            new LinkedHashSet<ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>>(this.getUnequalCache());
        Iterator<ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>> unequalIt = newUnequalCache.iterator();
        while (unequalIt.hasNext()) {
            ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef> unequal = unequalIt.next();
            if (!usedReferences.contains(unequal.x) || !usedReferences.contains(unequal.y)) {
                unequalIt.remove();
            }
        }
        return
            new LLVMHeuristicRelationSet(
                this.getRelations()
            ).restrictRelationsToRefs(
                this.setRelations(
                    Collections.emptySet()
                ).setValues(
                    newValues
                ).setMemory(
                    newHeap
                ).setAssociations(
                    newAssocs,
                    newAssocOffsets
                ).setUnequalCache(
                    newUnequalCache
                ),
                usedReferences,
                this.getStrategyParamters(),
                aborter
            );
    }

    @Override
    public LLVMHeuristicState retainLiveVariables(boolean keepFunctionParameters) {
        return (LLVMHeuristicState)super.retainLiveVariables(keepFunctionParameters);
    }



    @Override
    public LLVMHeuristicState setProgramPosition(LLVMProgramPosition newProgramPos) {
        return
            new LLVMHeuristicState(
                this.getModule(),
                this.getAllocatedInCurrentFunctionFrameIndices(),
                newProgramPos,
                this.isRefined(),
                this.getIntegerState(),
                this.getTrapValues(),
                false,
                this.getAllocatedByMallocIndices(),
                null,
                this.getAllocationChangedSinceEntryStateMap(),
                this.getStrategyParamters()
            );
    }

    @Override
    public LLVMHeuristicState setProgramVariable(String varName, LLVMSymbolicVariable ref, LLVMType type) {
        if (ref instanceof LLVMHeuristicConstRef) {
            return (LLVMHeuristicState)super.setProgramVariable(varName, ref, type);
        }
        boolean unsigned = this.getModule().getUnsignedBitvectorVariables().contains(varName);
        return
            ((LLVMHeuristicState)super.setProgramVariable(varName, ref, type)).initializeValue(
                (LLVMHeuristicVariable)ref,
                type.getInitializedIntValue(unsigned, this.getStrategyParamters().useBoundedIntegers)
            );
    }

    @Override
    public LLVMHeuristicState setRefined(boolean refinedParam) {
        return
            new LLVMHeuristicState(
                this.getModule(),
                this.getAllocatedInCurrentFunctionFrameIndices(),
                this.getProgramPosition(),
                refinedParam,
                this.getIntegerState(),
                this.getTrapValues(),
                this.isAbstractRecursiveFunctionStart(),
                this.getAllocatedByMallocIndices(),
                null,
                this.getAllocationChangedSinceEntryStateMap(),
                this.getStrategyParamters()
            );
    }

    @Override
    public LLVMHeuristicState setSimpleHeapEntry(LLVMSimpleTerm from, LLVMType targetType, boolean unsigned, LLVMTerm to, Abortion aborter) {
        final LLVMHeuristicRelationFactory relationFactory = this.getRelationFactory();
        final LLVMHeuristicTermFactory termFactory = relationFactory.getTermFactory();
        final boolean useBoundedIntegers = this.getStrategyParamters().useBoundedIntegers;
        LLVMHeuristicState res =
            this.initializeValue(
                (LLVMHeuristicVariable)from,
                new LLVMPointerType(
                    targetType,
                    this.getModule().getPointerSize(),
                    null
                ).getInitializedIntValue(
                    true,
                    useBoundedIntegers
                ).removeZeroFromInteger()
            );
        // check whether we just constructed a String - then try to infer typical String knowledge
        if (to.equals(termFactory.zero())) {
            LLVMHeuristicRelationSet relsToRemove = new LLVMHeuristicRelationSet();
            LLVMHeuristicRelationSet relsToAdd = new LLVMHeuristicRelationSet();
            ImmutableList<LLVMAllocation> allocations = res.getAllocations();
            LLVMHeuristicRelationSet rels = new LLVMHeuristicRelationSet(res.getRelations());
            for (LLVMAllocation allocation : allocations) {
                if (!allocation.y.equals(from)) {
                    continue;
                }
                // yes, this is a String - do we have an allocation equation between upper and lower bound?
                for (LLVMHeuristicRelation allocEquation : rels.getEquations()) {
                    aborter.checkAbortion();
                    Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = allocEquation.getLhs().toLinear();
                    Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = allocEquation.getRhs().toLinear();
                    final LLVMHeuristicOperation op;
                    final BigInteger bridgeOffset;
                    if (from.equals(lhsLinear.x)) {
                        if (
                            !(rhsLinear.x instanceof LLVMHeuristicOperation)
                            || rhsLinear.z.compareTo(BigInteger.ONE) != 0
                            || rhsLinear.y.compareTo(BigInteger.ZERO) != 0
                            || lhsLinear.z.compareTo(BigInteger.ONE) != 0
                        ) {
                            continue;
                        }
                        op = (LLVMHeuristicOperation)rhsLinear.x;
                        bridgeOffset = lhsLinear.y;
                    } else if (from.equals(rhsLinear.x)) {
                        if (
                            !(lhsLinear.x instanceof LLVMHeuristicOperation)
                            || lhsLinear.z.compareTo(BigInteger.ONE) != 0
                            || lhsLinear.y.compareTo(BigInteger.ZERO) != 0
                            || rhsLinear.z.compareTo(BigInteger.ONE) != 0
                        ) {
                            continue;
                        }
                        op = (LLVMHeuristicOperation)lhsLinear.x;
                        bridgeOffset = rhsLinear.y;
                    } else {
                        continue;
                    }
                    if (op.getOperation() != ArithmeticOperationType.ADD) {
                        continue;
                    }
                    LLVMHeuristicTerm opLhs = op.getLhs();
                    LLVMHeuristicTerm opRhs = op.getRhs();
                    final LLVMHeuristicVariable bridge;
                    if (allocation.x.equals(opLhs) && opRhs instanceof LLVMHeuristicVarRef) {
                        bridge = (LLVMHeuristicVariable)opRhs;
                    } else if (allocation.x.equals(opRhs) && opLhs instanceof LLVMHeuristicVarRef) {
                        bridge = (LLVMHeuristicVariable)opLhs;
                    } else {
                        continue;
                    }
                    // yes, we have an allocation equation - do we have a weak directed inequality for the bridge?
                    for (LLVMHeuristicRelation bridgeRel : rels.getDirectedInequalities()) {
                        if (
                            !bridge.equals(bridgeRel.getLhs()) || !(bridgeRel.getRhs() instanceof LLVMHeuristicVarRef)
                        ) {
                            continue;
                        }
                        // yes, we have a bridge relation
                        // do we have a further allocation relation with the other side of the bridge?
                        for (LLVMAllocation otherAllocation : allocations) {
                            // == is sufficient here as all allocations must have distinct variables
                            if (otherAllocation == allocation) {
                                continue;
                            }
                            for (LLVMHeuristicRelation otherEquation : rels.getEquations()) {
                                aborter.checkAbortion();
                                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> otherLhsLinear =
                                    otherEquation.getLhs().toLinear();
                                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> otherRhsLinear =
                                    otherEquation.getRhs().toLinear();
                                final LLVMHeuristicOperation otherOp;
                                if (otherAllocation.y.equals(otherLhsLinear.x)) {
                                    if (
                                        !(otherRhsLinear.x instanceof LLVMHeuristicOperation)
                                        || otherRhsLinear.z.compareTo(BigInteger.ONE) != 0
                                        || otherRhsLinear.y.compareTo(BigInteger.ZERO) != 0
                                        || otherLhsLinear.z.compareTo(BigInteger.ONE) != 0
                                        || otherLhsLinear.y.compareTo(bridgeOffset) != 0
                                    ) {
                                        continue;
                                    }
                                    otherOp = (LLVMHeuristicOperation)otherRhsLinear.x;
                                } else if (otherAllocation.y.equals(otherRhsLinear.x)) {
                                    if (
                                        !(otherLhsLinear.x instanceof LLVMHeuristicOperation)
                                        || otherLhsLinear.z.compareTo(BigInteger.ONE) != 0
                                        || otherLhsLinear.y.compareTo(BigInteger.ZERO) != 0
                                        || otherRhsLinear.z.compareTo(BigInteger.ONE) != 0
                                        || otherRhsLinear.y.compareTo(bridgeOffset) != 0
                                    ) {
                                        continue;
                                    }
                                    otherOp = (LLVMHeuristicOperation)otherLhsLinear.x;
                                } else {
                                    continue;
                                }
                                if (otherOp.getOperation() != ArithmeticOperationType.ADD) {
                                    continue;
                                }
                                if (
                                    (
                                        otherAllocation.x.equals(otherOp.getLhs())
                                        && bridgeRel.getRhs().equals(otherOp.getRhs())
                                    ) || (
                                        otherAllocation.x.equals(otherOp.getRhs())
                                        && bridgeRel.getRhs().equals(otherOp.getLhs())
                                    )
                                ) {
                                    // we have a String whose length is <= that of another allocated area
                                    relsToRemove.add(allocEquation);
                                    relsToRemove.add(otherEquation);
                                    relsToAdd.add(
                                        relationFactory.lessThanEquals(
                                            termFactory.add(otherAllocation.x, allocation.y),
                                            termFactory.add(allocation.x, otherAllocation.y)
                                        )
                                    );
                                }
                            }
                        }
                    }
                }
            }
            if (!relsToAdd.isEmpty()) {
                rels.removeAll(relsToRemove);
                rels.addAll(relsToAdd);
                res = res.setRelations(rels);
            }
        }
        Map<LLVMMemoryRange, LLVMMemoryInvariant> newHeap =
            new LinkedHashMap<LLVMMemoryRange, LLVMMemoryInvariant>(res.getMemory());
        if (to instanceof LLVMHeuristicConstRef) {
            newHeap.put(
                new LLVMMemoryRange(from, from, targetType, unsigned), new LLVMSimpleMemoryInvariant((LLVMHeuristicConstRef)to)
            );
            return res.setMemory(newHeap);
        }
        LLVMSymbolicVariable fresh = termFactory.freshVariable();
        newHeap.put(new LLVMMemoryRange(from, from, targetType, unsigned), new LLVMSimpleMemoryInvariant(fresh));
        // this needs to be done before the dereference
        res = res.setMemory(newHeap).addRelation(relationFactory.equalTo(fresh, to), aborter);
        LLVMHeuristicVariable pointedToVar = res.getDereferencedAccessSimple(from, targetType, unsigned, aborter);
        LLVMValue pointedToVal = targetType.getInitializedIntValue(unsigned, useBoundedIntegers);
        LLVMMemoryInvariant struct = res.getStructWithNextPointer(from);
        if (struct != null) {
            LLVMMemoryInvariant inv = ((LLVMCombinedMemoryInvariant)struct).getInvariantWithOffset(BigInteger.ZERO);
            if (inv instanceof LLVMComplexMemoryInvariant) {
                LLVMComplexMemoryInvariant compInv = (LLVMComplexMemoryInvariant) inv;
                if (compInv.getFirstValue() != null) {
                    if (compInv.getChange().getLinearRate() != null) {
                        LLVMRelation rel =
                            relationFactory.createAdditionRelation(
                                pointedToVar,
                                compInv.getFirstValue(),
                                termFactory.constant(compInv.getChange().getLinearRate())
                            );
                        res = res.addRelation(rel, aborter);
                    } else {
                        LLVMHeuristicRelation rel = null;
                        if (compInv.getChange().isAscending()) {
                            rel = relationFactory.lessThan(compInv.getFirstValue(), pointedToVar);
                        } else if (compInv.getChange().isDescending()) {
                            rel = relationFactory.lessThan(pointedToVar, compInv.getFirstValue());
                        } else if (compInv.getChange().isNonAscending()) {
                            rel = relationFactory.lessThanEquals(pointedToVar, compInv.getFirstValue());
                        } else if (compInv.getChange().isNonDescending()) {
                            rel = relationFactory.lessThanEquals(compInv.getFirstValue(), pointedToVar);
                        }
                        if (rel != null) {
                            res = res.addRelation(rel, aborter);
                        }
                    }
                }
            }
        }
        return res.initializeValue(pointedToVar, pointedToVal);
    }

    /**
     * @param ref The reference to map.
     * @param val The value to map the reference to.
     * @return An AbstractState with the new value mapping, but everything else as in the current state.
     */
    public LLVMHeuristicState setValue(LLVMHeuristicVariable ref, LLVMValue val) {
        if (Globals.useAssertions) {
            assert (!(ref.isConcrete() && this.isPossiblyTrapValue(ref))) :
                "Trap values cannot be assigned to concrete references!";
        }
        return this.setIntegerState(this.getIntegerState().setValue(ref, val));
    }

    @Override
    public JSONObject toJSON() {
        JSONObject res = super.toJSON();
        res.put("type", "LLVMHeuristicState");
        return res;
    }

    /**
     * Attention: this method might yield tautological relations which must be cleaned thereafter!
     * @param firstVar One variable.
     * @param secondVar Another variable.
     * @return An AbstractState where both specified variables are equal (i.e., one is replaced by the other and the
     *         values are intersected) and a map indicating which variable has been replaced by which. The replacement
     *         might induce further replacements according to heap information.
     */
    public LLVMReplacementResult unifySymbolicVariables(LLVMHeuristicVariable firstVar, LLVMHeuristicVariable secondVar) {
        if (firstVar.equals(secondVar)) {
            return new LLVMReplacementResult(this, Collections.<LLVMHeuristicVariable, LLVMHeuristicVariable>emptyMap());
        }
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements =
            new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>();
        LLVMHeuristicState.computeReplacements(this.getMemory(), firstVar, secondVar, replacements);
        // now make union-find structure a well-formed substitution
        for (LLVMHeuristicVariable ref : new LinkedHashSet<LLVMHeuristicVariable>(replacements.keySet())) {
            // use path compression
            LLVMHeuristicState.find(replacements, ref);
        }
        // remove loops
        Iterator<Map.Entry<LLVMHeuristicVariable, LLVMHeuristicVariable>> it = replacements.entrySet().iterator();
        while (it.hasNext()) {
            Map.Entry<LLVMHeuristicVariable, LLVMHeuristicVariable> entry = it.next();
            if (entry.getKey().equals(entry.getValue())) {
                it.remove();
            }
        }
        // the replacements are updated within replaceReferences
        return new LLVMReplacementResult(this.replaceReferences(replacements), replacements);
    }

    @Override
    public LLVMHeuristicState updateTrapValues(Abortion aborter) {
        return (LLVMHeuristicState)super.updateTrapValues(aborter);
    }

    /**
     * @param ref A reference whose value interval has just changed.
     * @param newRels The newly learned relations.
     * @return A state emerging from this state by adjusting other value intervals according to the changed interval
     *         and known equations.
     */
    public LLVMHeuristicState updateValuesAccordingToEquations(
        LLVMHeuristicVariable ref,
        Set<LLVMHeuristicRelation> newRels
    ) {
        LLVMHeuristicState res = this;
        Set<LLVMHeuristicVariable> changed = new LinkedHashSet<LLVMHeuristicVariable>();
        // TODO this statement might lead to a cast exception as soon as we have other values than integers
        LLVMValue value = res.getValue(ref);
        AbstractBoundedInt val = value.getThisAsAbstractBoundedInt();
        if (Globals.useAssertions && LLVMDebuggingFlags.CHECK_INVARIANTS) {
            assert (val != null) : "Found reference not occurring in the value function of this state!";
        }
        IntervalBound lower = val.getLower();
        IntervalBound upper = val.getUpper();
        for (LLVMHeuristicRelation rel : this.getRelations()) {
            if (!rel.isEquation()) {
                continue;
            }
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = rel.getLhs().toLinear();
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = rel.getRhs().toLinear();
            if (
                lhsLinear.x == null
                || rhsLinear.x == null
                || lhsLinear.z.compareTo(BigInteger.ONE) != 0
                || rhsLinear.z.compareTo(BigInteger.ONE) != 0
            ) {
                continue;
            }
            if (lhsLinear.x.equals(ref) && rhsLinear.x instanceof LLVMHeuristicVariable) {
                Pair<LLVMHeuristicState, Boolean> pair =
                    res.updateValuesAccordingToSpecifiedEquation(
                        ref,
                        value,
                        val,
                        lower,
                        upper,
                        lhsLinear.y,
                        new Pair<LLVMHeuristicVariable, BigInteger>((LLVMHeuristicVariable)rhsLinear.x, rhsLinear.y),
                        changed,
                        newRels
                    );
                res = pair.x;
                if (pair.y) {
                    break;
                }
            } else if (rhsLinear.x.equals(ref) && lhsLinear.x instanceof LLVMHeuristicVariable) {
                Pair<LLVMHeuristicState, Boolean> pair =
                    res.updateValuesAccordingToSpecifiedEquation(
                        ref,
                        value,
                        val,
                        lower,
                        upper,
                        rhsLinear.y,
                        new Pair<LLVMHeuristicVariable, BigInteger>((LLVMHeuristicVariable)lhsLinear.x, lhsLinear.y),
                        changed,
                        newRels
                    );
                res = pair.x;
                if (pair.y) {
                    break;
                }
            }
        }
        for (LLVMHeuristicVariable changedRef : changed) {
            res = res.updateValuesAccordingToEquations(changedRef, newRels);
        }
        return res;
    }

    /**
     * This is a heuristic for using other heuristics (originally designed for array inequalities) on array equalities.
     * @return A state emerging from this state by weakening all equations of the form lower + ref = upper + 1 for some
     *         allocation (lower,upper) to lower + ref <= upper + 1. Null if no such equations exists.
     */
    public LLVMHeuristicState weakenAllocationEquations() {
        LLVMHeuristicRelationSet toRemove = new LLVMHeuristicRelationSet();
        LLVMHeuristicRelationSet toAdd = new LLVMHeuristicRelationSet();
        LLVMHeuristicRelationSet rels = new LLVMHeuristicRelationSet(this.getRelations());
        final LLVMHeuristicRelationFactory relationFactory = this.getRelationFactory();
        for (LLVMHeuristicRelation rel : rels.getEquations()) {
            Pair<LLVMHeuristicTerm, LLVMHeuristicTerm> allocationEquation =
                LLVMHeuristicExpressionUtils.checkAllocationEquation(rel, this.getAllocations());
            if (allocationEquation != null) {
                toRemove.add(rel);
                toAdd.add(relationFactory.lessThanEquals(allocationEquation.x, allocationEquation.y));
            }
        }
        if (toAdd.isEmpty()) {
            return null;
        }
        rels.removeAll(toRemove);
        rels.addAll(toAdd);
        return this.setRelations(rels);
    }

    /**
     * Adds a set of relations to the state.
     * @param rels The relations to add.
     * @return The AbstractState where the relations were added and the set of really added relations (those relations
     *         which were already implied are not added). Moreover, if some strict directed inequalities between
     *         references or any directed inequalities between a reference and a constant are contained in the
     *         specified set of relations, we try to add further implied associations of yet unassociated pointer
     *         references.
     */
    protected LLVMSymbolicEvaluationResult addRelations(Set<LLVMHeuristicRelation> rels, Abortion aborter) {
        LLVMHeuristicRelationSet newRels = new LLVMHeuristicRelationSet(this.getRelations());
        LLVMHeuristicRelationSet res =
            newRels.addRelations(this.getIntegerState(), rels, true, aborter);
        if (res.isEmpty()) {
            return new LLVMSymbolicEvaluationResult(this, res);
        } else {
            Set<LLVMRelation> addedRels = new LinkedHashSet<>(res);
            LLVMAbstractState newState = this.setRelations(newRels).findFurtherAssociations(res, addedRels, aborter); 
            return new LLVMSymbolicEvaluationResult(newState, addedRels);
        }
    }

    /**
     * @param possiblyFresh Some symbolic variable.
     * @param initialValue The initial value for the symbolic variable.
     * @return This state where the value of the specified symbolic variable is set to the specified initial value if
     *         there has not been some value set for that variable before. Otherwise, this state is returned without
     *         modification.
     */
    protected LLVMHeuristicState initializeValue(LLVMHeuristicVariable possiblyFresh, LLVMValue initialValue) {
        return this.setIntegerState(this.getIntegerState().initializeValue(possiblyFresh, initialValue));
    }

    @Override
    protected LLVMSymbolicEvaluationResult postProcess(LLVMSymbolicEvaluationResult res, Set<? extends LLVMRelation> instructionRels, boolean removeNonLiveVariables, Abortion aborter) {
        final LLVMSymbolicEvaluationResult newRes = super.postProcess(res, instructionRels, removeNonLiveVariables, aborter);
        // note that the used references computed here are the old ones (i.e., of this)
        // the ones for the new state are computed within the restrictToUsedReferences method
        final LLVMHeuristicRelationFactory relationFactory = this.getRelationFactory();
        final LLVMHeuristicTermFactory termFactory = relationFactory.getTermFactory();
        final LLVMHeuristicState state = (LLVMHeuristicState)newRes.x;
        final LLVMKnowledgeResult pre = state.simplify(instructionRels);
        final LLVMKnowledgeResult k =
            pre.x.restrictToUsedReferences(pre.x.getValues().keySet(), aborter).cleanRelations(aborter).adjustValues(aborter);
        k.y.putAll(pre.y);
        k.z.putAll(pre.z);
        // create new set as the one in the evaluation result might be immutable
        Set<LLVMRelation> rels = new LinkedHashSet<LLVMRelation>(newRes.y);
        for (Map.Entry<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> entry : k.y.entrySet()) {
            Pair<BigInteger, BigInteger> value = entry.getValue();
            if (value.x != null) {
                rels.add(relationFactory.lessThanEquals(termFactory.constant(value.x), entry.getKey()));
            }
            if (value.y != null) {
                rels.add(relationFactory.lessThanEquals(entry.getKey(), termFactory.constant(value.y)));
            }
        }
        for (Map.Entry<LLVMHeuristicVariable, LLVMHeuristicVariable> entry : k.z.entrySet()) {
            rels.add(relationFactory.equalTo(entry.getKey(), entry.getValue()));
        }
        newRes.x = k.x;
        newRes.y = rels;
        return newRes;
    }

    @Override
    protected LLVMHeuristicState removeAllocation(int index, Abortion aborter) {
        LLVMHeuristicState res = (LLVMHeuristicState)super.removeAllocation(index, aborter);
        Map<LLVMHeuristicVariable, Integer> newAssocs =
            new LinkedHashMap<LLVMHeuristicVariable, Integer>(this.getAssociations());
        Map<LLVMHeuristicVariable, BigInteger> newAssocOffsets =
            new LinkedHashMap<LLVMHeuristicVariable, BigInteger>(this.getAssociationOffsets());
        Iterator<Map.Entry<LLVMHeuristicVariable, Integer>> assocIt = newAssocs.entrySet().iterator();
        while (assocIt.hasNext()) {
            Map.Entry<LLVMHeuristicVariable, Integer> next = assocIt.next();
            int value = next.getValue();
            if (value == index) {
                assocIt.remove();
                newAssocOffsets.remove(next.getKey());
            } else if (value > index) {
                next.setValue(value - 1);
            }
        }
        return res.setAssociations(newAssocs, newAssocOffsets);
    }

    @Override
    protected LLVMHeuristicState setAllocatedMemoryForAlloca(
        List<LLVMAllocation> newAllocs,
        TreeSet<Integer> newFrameAllocs
    ) {
        return (LLVMHeuristicState)super.setAllocatedMemoryForAlloca(newAllocs, newFrameAllocs);
    }

    @Override
    protected LLVMHeuristicState setAllocatedMemoryForAllocaAndMalloc(
        List<LLVMAllocation> newAllocs,
        TreeSet<Integer> newFrameAllocs,
        TreeSet<Integer> newAllocatedByMalloc
    ) {
        return
            new LLVMHeuristicState(
                this.getModule(),
                ImmutableCreator.create(newFrameAllocs),
                this.getProgramPosition(),
                this.isRefined(),
                this.getIntegerState().setAllocations(newAllocs),
                this.getTrapValues(),
                this.isAbstractRecursiveFunctionStart(),
                ImmutableCreator.create(newAllocatedByMalloc),
                null,
                this.getAllocationChangedSinceEntryStateMap(),
                this.getStrategyParamters()
            );
    }

    @Override
    protected LLVMHeuristicState setAllocatedMemoryForMalloc(
        List<LLVMAllocation> newAllocs,
        TreeSet<Integer> newAllocatedByMalloc
    ) {
        return (LLVMHeuristicState)super.setAllocatedMemoryForMalloc(newAllocs, newAllocatedByMalloc);
    }

    /**
     * @param newAssocs The new associations.
     * @param newAssocOffsets The new association offsets.
     * @return An abstract state with the new associations and offsets and everything else as in the current state.
     */
    protected LLVMHeuristicState setAssociations(
        Map<LLVMHeuristicVariable, Integer> newAssocs,
        Map<LLVMHeuristicVariable, BigInteger> newAssocOffsets
    ) {
        return
            this.setIntegerState(
                this.getIntegerState().setAssociations(newAssocs).setAssociationOffsets(newAssocOffsets)
            );
    }

    @Override
    protected LLVMHeuristicState setCallStack(Deque<LLVMReturnInformation> newCallStack) {
        return this.setIntegerState(this.getIntegerState().setCallStack(newCallStack));
    }

    @Override
    protected LLVMHeuristicState setMemory(Map<LLVMMemoryRange, LLVMMemoryInvariant> newHeap) {
        return this.setIntegerState(this.getIntegerState().setMemory(newHeap));
    }

    /**
     * @param newInitHeapAddrs The new initial heap addresses.
     * @return A state with the specified initial heap addresses and everything else as in the current state.
     */
    protected LLVMHeuristicState setInitialHeapAddresses(Map<Integer, LLVMHeuristicVariable> newInitHeapAddrs) {
        return this.setIntegerState(this.getIntegerState().setInitialHeapAddresses(newInitHeapAddrs));
    }

    @Override
    protected LLVMHeuristicState setIntegerState(LLVMIntegerState iState) {
        return
            new LLVMHeuristicState(
                this.getModule(),
                this.getAllocatedInCurrentFunctionFrameIndices(),
                this.getProgramPosition(),
                this.isRefined(),
                (LLVMHeuristicIntegerState)iState,
                this.getTrapValues(),
                this.isAbstractRecursiveFunctionStart(),
                this.getAllocatedByMallocIndices(),
                null,
                this.getAllocationChangedSinceEntryStateMap(),
                this.getStrategyParamters()
            );
    }

    /**
     * @param vars The new program variable function.
     * @return This state with the specified program variable function instead of its current one.
     */
    @Override
    protected LLVMHeuristicState setProgramVariables(
        Map<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> vars
    ) {
        return this.setIntegerState(this.getIntegerState().setProgramVariables(vars));
    }

    /**
     * Call this method only with relations not encoding mere value changes!
     * @param rels The new relations.
     * @return This state where the relation set has been set to the specified one.
     */
    protected LLVMHeuristicState setRelations(Set<LLVMHeuristicRelation> rels) {
        return this.setIntegerState(this.getIntegerState().setRelations(rels));
    }

    @Override
    protected LLVMHeuristicState setTrapValues(Map<LLVMSymbolicVariable, LLVMTrapCondition> trapVals) {
        return
            new LLVMHeuristicState(
                this.getModule(),
                this.getAllocatedInCurrentFunctionFrameIndices(),
                this.getProgramPosition(),
                this.isRefined(),
                this.getIntegerState(),
                ImmutableCreator.create(trapVals),
                this.isAbstractRecursiveFunctionStart(),
                this.getAllocatedByMallocIndices(),
                null,
                this.getAllocationChangedSinceEntryStateMap(),
                this.getStrategyParamters()
            );
    }

    /**
     * @param newUnequalCache The new cache for unequal variables.
     * @return This state where the cache for unequal variables has been set to the specified one.
     */
    protected LLVMHeuristicState setUnequalCache(
        Set<ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>> newUnequalCache) {
        return this.setIntegerState(this.getIntegerState().setUnequalCache(newUnequalCache));
    }

    /**
     * @param newValues The new values.
     * @return This state where the values have been set to the specified ones.
     */
    protected LLVMHeuristicState setValues(Map<LLVMHeuristicVariable, LLVMValue> newValues) {
        return this.setIntegerState(this.getIntegerState().setValues(newValues));
    }
    
    /**
     * @return The state emerging from this state by simplifying only the given relations.
     */
    public LLVMKnowledgeResult simplify(Set<? extends LLVMRelation> rels) {
        LLVMHeuristicState res = this;
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> shrinking =
            new LinkedHashMap<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>>();
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements =
            new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>();
        final LLVMHeuristicRelationFactory relationFactory = this.getRelationFactory();
        final LLVMHeuristicTermFactory termFactory = relationFactory.getTermFactory();
        for (LLVMRelation r : rels) {
            LLVMHeuristicRelation rel = (LLVMHeuristicRelation) r;
            if (rel.isSimpleArithmeticEquation()) {
                for (LLVMHeuristicVariable var : rel.getVariables(false)) {
                    if (rel.solveFor(var) == null) {
                        continue;
                    }
                    LLVMHeuristicOperation op = (LLVMHeuristicOperation) (rel.solveFor(var)).x;
                    if (op.getOperation() == ArithmeticOperationType.ADD) {
                        LLVMHeuristicTerm lhs = op.getLhs();
                        LLVMHeuristicTerm rhs = op.getRhs();
                        LLVMHeuristicVarRef minuend;
                        LLVMHeuristicVarRef subtrahend;
                        if (lhs instanceof LLVMHeuristicVarRef && rhs.isNegatedVariable()) {
                            minuend = (LLVMHeuristicVarRef) lhs;
                            assert (rhs.getVariables(false).size() == 1);
                            subtrahend = (LLVMHeuristicVarRef) rhs.getVariables(false).iterator().next();
                        } else if (lhs.isNegatedVariable() && rhs instanceof LLVMHeuristicVarRef) {
                            minuend = (LLVMHeuristicVarRef) rhs;
                            assert (lhs.getVariables(false).size() == 1);
                            subtrahend = (LLVMHeuristicVarRef) lhs.getVariables(false).iterator().next();
                        } else {
                            continue;
                        }
                        // var = minuend - subtrahend
                        LLVMHeuristicVariable var1;
                        LLVMHeuristicVariable var2;
                        LLVMHeuristicOperation op1;
                        LLVMHeuristicOperation op2;
                        // find rel1 such that minuend = op1 and rel2 such that subtrahend = op2
                        for (LLVMHeuristicRelation rel1 : this.getRelations()) {
                            if (!rel1.isSimpleArithmeticEquation()) {
                                continue;
                            }
                            if (rel1.getLhs() instanceof LLVMHeuristicVariable) {
                                var1 = (LLVMHeuristicVariable) rel1.getLhs();
                                op1 = (LLVMHeuristicOperation) rel1.getRhs();
                            } else {
                                var1 = (LLVMHeuristicVariable) rel1.getRhs();
                                op1 = (LLVMHeuristicOperation) rel1.getLhs();
                            }
                            if (!var1.equals(minuend)) {
                                continue;
                            }
                            for (LLVMHeuristicRelation rel2 : this.getRelations()) {
                                if (!rel2.isSimpleArithmeticEquation()) {
                                    continue;
                                }
                                if (rel2.getLhs() instanceof LLVMHeuristicVariable) {
                                    var2 = (LLVMHeuristicVariable) rel2.getLhs();
                                    op2 = (LLVMHeuristicOperation) rel2.getRhs();
                                } else {
                                    var2 = (LLVMHeuristicVariable) rel2.getRhs();
                                    op2 = (LLVMHeuristicOperation) rel2.getLhs();
                                }
                                if (!var2.equals(subtrahend)) {
                                    continue;
                                }
                                LLVMHeuristicTerm t = termFactory.create(ArithmeticOperationType.SUB, op1, op2);
                                if (t instanceof LLVMHeuristicVariable) {
                                    LLVMReplacementResult repRes = this.unifySymbolicVariables(var, (LLVMHeuristicVariable)t);
                                    LLVMHeuristicState nextState = repRes.x;
                                    if (this.isPossiblyTrapValue(var)) {
                                        if (repRes.y.containsKey(var)) {
                                            LLVMHeuristicVariable replacementRef = repRes.y.get(var);
                                            try {
                                                nextState = nextState.putTrapValue(replacementRef, this.getTrapValues().get(var));
                                            } catch (UndefinedBehaviorException e) {
                                                throw new IllegalStateException("Could not simplify relation due to too many trap values!");
                                            }
                                        }
                                    }
                                    shrinking.keySet().removeAll(repRes.y.keySet());
                                    return new LLVMKnowledgeResult(nextState, shrinking, repRes.y);
                                }
                            }
                        }
                    }
                }
            }
        }
        return new LLVMKnowledgeResult(res, shrinking, replacements);
    }

    /**
     * @param unassociatedAccessIterator Iterator over yet unassociated memory accesses.
     * @param left The left border of the allocation.
     * @param right The right border of the allocation.
     * @param association The index of the specified allocation within the allocation list.
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @return A state emerging from this state by adding further associations to yet unassociated memory accesses in
     *         case we can prove that these are between the allocation border variables.
     */
    private LLVMHeuristicState addFurtherAssociations(
        Iterator<Map.Entry<LLVMHeuristicVariable, TreeSet<LLVMPointerType>>> unassociatedAccessIterator,
        LLVMHeuristicVariable left,
        LLVMHeuristicVariable right,
        Integer association,
        Set<LLVMRelation> newRels,
        Abortion aborter
    ) {
        LLVMHeuristicState res = this;
        while (unassociatedAccessIterator.hasNext()) {
            aborter.checkAbortion();
            Map.Entry<LLVMHeuristicVariable, TreeSet<LLVMPointerType>> access = unassociatedAccessIterator.next();
            res = res.possiblyAddAssociation(access, left, right, association, newRels, aborter);
            if (access.getValue().isEmpty()) {
                unassociatedAccessIterator.remove();
            }
        }
        return res;
    }

    /**
     * @param ref Some reference.
     * @param expr An expression in relation to <code>ref</code>.
     * @param greater Indicates the relation type. The meaning of <code>null</code> is <code>ref = expr</code>,
     *                <code>true</code> means <code>ref >= expr</code>, <code>false</code> means
     *                <code>ref <= expr</code>.
     * @return The state emerging from this state by adjusting the value of <code>ref</code> such that it is consistent
     *         with the specified relation, newly learned relations between references and constants expressing the
     *         shrinking of values, and a map of replacements conducted (this occurs if some reference is known to be a
     *         constant by adding the specified relation).
     */
    private LLVMKnowledgeResult adjustValue(LLVMHeuristicVariable ref, LLVMHeuristicTerm expr, Boolean greater) {
        LLVMValue refValue = this.getValue(ref);
        AbstractBoundedInt refVal = refValue.getThisAsAbstractBoundedInt();
        IntervalBound refLower = refVal.getLower();
        BigInteger lower = refLower.isFinite() ? refLower.getConstant() : null;
        BigInteger origLower = lower;
        IntervalBound refUpper = refVal.getUpper();
        BigInteger upper = refUpper.isFinite() ? refUpper.getConstant() : null;
        BigInteger origUpper = upper;
        if (greater == null) {
            Set<LLVMHeuristicTerm> greaterExprSet =
                LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(expr, this.getValues(), false, true);
            greaterExprSet.addAll(LLVMHeuristicExpressionUtils.inRelationByInequality(expr, this.getRelations(), false, true));
            for (LLVMHeuristicTerm greaterExpr : greaterExprSet) {
                // ref = expr >= greaterExpr
                if (!(greaterExpr instanceof LLVMHeuristicConstRef)) {
                    continue;
                }
                BigInteger val = ((LLVMHeuristicConstRef)greaterExpr).getIntegerValue();
                if (lower == null || lower.compareTo(val) < 0) {
                    lower = val;
                }
            }
            Set<LLVMHeuristicTerm> lessExprSet =
                LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(expr, this.getValues(), false, false);
            lessExprSet.addAll(LLVMHeuristicExpressionUtils.inRelationByInequality(expr, this.getRelations(), false, false));
            for (LLVMHeuristicTerm lessExpr : lessExprSet) {
                // ref = expr <= lessExpr
                if (!(lessExpr instanceof LLVMHeuristicConstRef)) {
                    continue;
                }
                BigInteger val = ((LLVMHeuristicConstRef)lessExpr).getIntegerValue();
                if (upper == null || upper.compareTo(val) > 0) {
                    upper = val;
                }
            }
        } else if (greater) {
            for (
                LLVMHeuristicTerm greaterExpr :
                    LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(expr, this.getValues(), false, true)
            ) {
                // ref >= expr >= greaterExpr
                if (!(greaterExpr instanceof LLVMHeuristicConstRef)) {
                    continue;
                }
                BigInteger val = ((LLVMHeuristicConstRef)greaterExpr).getIntegerValue();
                if (lower == null || lower.compareTo(val) < 0) {
                    lower = val;
                }
            }
        } else {
            for (
                LLVMHeuristicTerm lessExpr :
                    LLVMHeuristicExpressionUtils.inRelationByReplacingRefsByConstants(expr, this.getValues(), false, false)
            ) {
                // ref <= expr <= lessExpr
                if (!(lessExpr instanceof LLVMHeuristicConstRef)) {
                    continue;
                }
                BigInteger val = ((LLVMHeuristicConstRef)lessExpr).getIntegerValue();
                if (upper == null || upper.compareTo(val) > 0) {
                    upper = val;
                }
            }
        }
        boolean changed = false;
        if (lower != null && (origLower == null || origLower.compareTo(lower) < 0)) {
            refVal = refVal.setLower(IntervalBound.create(lower));
            if(refVal == null) {
            	throw new InconsistentStateException(null, null);
            }
            changed = true;
        } else {
            lower = null;
        }
        if (upper != null && (origUpper == null || origUpper.compareTo(upper) > 0)) {
            refVal = refVal.setUpper(IntervalBound.create(upper));
            if(refVal == null)
            	throw new InconsistentStateException(null, null);
            changed = true;
        } else {
            upper = null;
        }
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> shrinking =
            new LinkedHashMap<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>>();
        if (changed) {
            if (refVal.isIntLiteral()) {
                LLVMReplacementResult repRes =
                    this.unifySymbolicVariables(
                        ref,
                        this.getRelationFactory().getTermFactory().constant(refVal.getIntLiteralValue())
                    );
                LLVMHeuristicState nextState = repRes.x;
                if (this.isPossiblyTrapValue(ref)) {
                    if (repRes.y.containsKey(ref)) {
                        LLVMHeuristicVariable replacementRef = repRes.y.get(ref);
                        try {
                            nextState = nextState.putTrapValue(replacementRef, this.getTrapValues().get(ref));
                        } catch (UndefinedBehaviorException e) {
                            throw new IllegalStateException("Could not adjust values due to too many trap values!");
                        }
                    }
                }
                shrinking.keySet().removeAll(repRes.y.keySet());
                return new LLVMKnowledgeResult(nextState, shrinking, repRes.y);
            }
            if (shrinking.containsKey(ref)) {
                Pair<BigInteger, BigInteger> old = shrinking.get(ref);
                if (lower != null) {
                    if (old.x == null || old.x.compareTo(lower) < 0) {
                        old.x = lower;
                    }
                }
                if (upper != null) {
                    if (old.y == null || old.y.compareTo(upper) > 0) {
                        old.y = upper;
                    }
                }
                if (old.x != null && old.y != null && old.x.compareTo(old.y) == 0) {
                    LLVMReplacementResult repRes =
                        this.unifySymbolicVariables(ref, this.getRelationFactory().getTermFactory().constant(old.x));
                    shrinking.keySet().removeAll(repRes.y.keySet());
                    return new LLVMKnowledgeResult(repRes.x, shrinking, repRes.y);
                }
            } else {
                shrinking.put(ref, new Pair<BigInteger, BigInteger>(lower, upper));
            }
            return new LLVMKnowledgeResult(
                this.setValue(ref, refVal),
                shrinking,
                Collections.<LLVMHeuristicVariable, LLVMHeuristicVariable>emptyMap()
            );
        }
        return
            new LLVMKnowledgeResult(this, shrinking, Collections.<LLVMHeuristicVariable, LLVMHeuristicVariable>emptyMap());
    }

    /**
     * @param ref Some reference.
     * @param op Some operation.
     * @param shrinking The shrinking.
     * @param replacements The replacements.
     * @param params Strategy parameters.
     * @return If the operation is an addition and satisfies the multiplication and inequality pattern together with
     *         ref, then zero is removed from a reference inside the operation in the resulting state. Otherwise, just
     *         the specified state is returned unchanged.
     */
    private LLVMHeuristicState checkMultiplicationAndPointerInequalityCase(
        LLVMHeuristicVarRef ref,
        LLVMHeuristicOperation op,
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> shrinking,
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements,
        Abortion aborter
    ) {
        LLVMHeuristicState res = this;
        if (op.getOperation() == ArithmeticOperationType.ADD) {
            LLVMHeuristicTerm opLhs = op.getLhs();
            LLVMHeuristicTerm opRhs = op.getRhs();
            if (opLhs instanceof LLVMHeuristicVarRef) {
                res =
                    res.checkMultiplicationAndPointerInequalityCase(
                        ref,
                        (LLVMHeuristicVarRef)opLhs,
                        opRhs.toLinear(),
                        shrinking,
                        replacements,
                        aborter
                    );
            }
            if (opRhs instanceof LLVMHeuristicVarRef) {
                res =
                    res.checkMultiplicationAndPointerInequalityCase(
                        ref,
                        (LLVMHeuristicVarRef)opRhs,
                        opLhs.toLinear(),
                        shrinking,
                        replacements,
                        aborter
                    );
            }
        }
        return res;
    }

    /**
     * @param ref1 Some reference.
     * @param ref2 Another reference.
     * @param linear A linear expression. All in all, we know ref1 = ref2 + linear.
     * @param shrinking The shrinking map.
     * @param replacements The replacements to constants.
     * @param params Strategy parameters.
     * @return If the non-constant part of linear is a reference whose value contains zero, the constant part of 
     *         linear is zero, and the two references are known to be unequal, then zero is removed from the linear 
     *         reference's value in the resulting state. Otherwise, just the specified state is returned unchanged.
     */
    private LLVMHeuristicState checkMultiplicationAndPointerInequalityCase(
        LLVMHeuristicVarRef ref1,
        LLVMHeuristicVarRef ref2,
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> linear,
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> shrinking,
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements,
        Abortion aborter
    ) {
        if (!(linear.x instanceof LLVMHeuristicVarRef)) {
            return this;
        }
        LLVMHeuristicVarRef ref = (LLVMHeuristicVarRef)linear.x;
        AbstractBoundedInt value = this.getValue(ref).getThisAsAbstractBoundedInt();
        LLVMHeuristicState res = this;
        if (value.containsLiteral(BigInteger.ZERO) && linear.y.equals(BigInteger.ZERO)) {
            Pair<Boolean, ? extends LLVMAbstractState> check =
                res.checkRelation(res.getRelationFactory().notEqualTo(ref1, ref2), aborter);
            if (check.x) {
                res = (LLVMHeuristicState)check.y;
                if (value.isNonNegative()) {
                    if (shrinking.containsKey(ref)) {
                        Pair<BigInteger, BigInteger> pair = shrinking.get(ref);
                        pair.x = BigInteger.ONE;
                        shrinking.put(ref, pair);
                    } else {
                        shrinking.put(ref, new Pair<BigInteger, BigInteger>(BigInteger.ONE, null));
                    }
                } else if (value.isNonPositive()) {
                    if (shrinking.containsKey(ref)) {
                        Pair<BigInteger, BigInteger> pair = shrinking.get(ref);
                        pair.y = IntegerUtils.NEGONE;
                        shrinking.put(ref, pair);
                    } else {
                        shrinking.put(ref, new Pair<BigInteger, BigInteger>(null, IntegerUtils.NEGONE));
                    }
                }
                return res.setValue(ref, value.removeZeroFromInteger());
            }
        }
        return res;
    }

    /**
     * @param rel Some relation.
     * @return A triple of first the state emerging from this state by shrinking the value intervals such that they are
     *         consistent with the specified relation, second the map storing the shrinking to non-constant values, and
     *         third the replacements to constants conducted.
     */
    private LLVMKnowledgeResult adjustValues(LLVMHeuristicRelation rel, Abortion aborter) {
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> shrinking =
            new LinkedHashMap<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>>();
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements =
            new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>();
        Triple<LLVMHeuristicVariable, BigInteger, Boolean> valChange = rel.checkValueRelation();
        if (valChange != null) {
            if (valChange.z == null) {
                LLVMReplacementResult repRes =
                    this.unifySymbolicVariables(
                        valChange.x,
                        this.getRelationFactory().getTermFactory().constant(valChange.y)
                    );
                return new LLVMKnowledgeResult(repRes.x, shrinking, repRes.y);
            } else if (valChange.z) {
                LLVMValue value = this.getValue(valChange.x);
                AbstractBoundedInt val = value.getThisAsAbstractBoundedInt();
                IntervalBound upper = val.getUpper();
                if (!upper.isFinite() || upper.getConstant().compareTo(valChange.y) > 0) {
                    shrinking.put(valChange.x, new Pair<BigInteger, BigInteger>(null, valChange.y));
                    LLVMValue nextVal = val.setUpper(IntervalBound.create(valChange.y));
                    if(nextVal == null)
                    	throw new InconsistentStateException(null, null);
                    return new LLVMKnowledgeResult(this.setValue(valChange.x, nextVal), shrinking, replacements);
                }
                return new LLVMKnowledgeResult(this, shrinking, replacements);
            } else {
                LLVMValue value = this.getValue(valChange.x);
                AbstractBoundedInt val = value.getThisAsAbstractBoundedInt();
                IntervalBound lower = val.getLower();
                if (!lower.isFinite() || lower.getConstant().compareTo(valChange.y) < 0) {
                    shrinking.put(valChange.x, new Pair<BigInteger, BigInteger>(valChange.y, null));
                    LLVMValue nextVal = val.setLower(IntervalBound.create(valChange.y));
                    if(nextVal == null) {
                    	throw new InconsistentStateException(null, null);
                    }
                    return new LLVMKnowledgeResult(this.setValue(valChange.x, nextVal), shrinking, replacements);
                }
                return new LLVMKnowledgeResult(this, shrinking, replacements);
            }
        }
        if (Globals.useAssertions && LLVMDebuggingFlags.CHECK_INVARIANTS) {
            assert (valChange == null) : "All cases for a simple value change should have been handled before!";
        }
        LLVMHeuristicState res = this;
        LLVMHeuristicRelation curRel = rel;
        outer: while (true) {
            aborter.checkAbortion();
            for (LLVMHeuristicVariable ref : curRel.getVariables(false)) {
                Pair<LLVMHeuristicTerm, Boolean> solved = curRel.solveFor(ref);
                if (solved != null) {
                    LLVMKnowledgeResult next = res.adjustValue(ref, solved.x, solved.y);
                    if (res != next.x) {
                        res = next.x;
                        LLVMHeuristicExpressionUtils.updateReplacements(replacements, next.z);
                        LLVMHeuristicExpressionUtils.updateReplacements(
                            replacements,
                            this.updateShrinking(shrinking, next.y)
                        );
                        curRel = curRel.applySubstitution(replacements);
                        continue outer;
                    }
                }
            }
            break;
        }
        if (curRel.isEquation()) {
            LLVMHeuristicTerm lhs = curRel.getLhs();
            LLVMHeuristicTerm rhs = curRel.getRhs();
            // check simple equation
            if (lhs instanceof LLVMHeuristicVarRef && rhs instanceof LLVMHeuristicVarRef) {
                res =
                    res.unifyReferences(
                        (LLVMHeuristicVariable)lhs,
                        (LLVMHeuristicVariable)rhs,
                        replacements,
                        shrinking
                    );
                // no further replacement of relation needed as nothing else is to be done
            } else {
                // check multiplications
                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = lhs.toLinear();
                Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = rhs.toLinear();
                if (lhsLinear.x instanceof LLVMHeuristicVariable && rhsLinear.x instanceof LLVMHeuristicVariable) {
                    LLVMHeuristicState nextState =
                        res.handleMultiplicationCase(
                            shrinking,
                            replacements,
                            (LLVMHeuristicVariable)lhsLinear.x,
                            lhsLinear.y,
                            lhsLinear.z,
                            (LLVMHeuristicVariable)rhsLinear.x,
                            rhsLinear.y,
                            rhsLinear.z
                        );
                    if (!res.equals(nextState)) {
                        res = nextState;
                        curRel = curRel.applySubstitution(replacements);
                        lhs = curRel.getLhs();
                        rhs = curRel.getRhs();
                        lhsLinear = lhs.toLinear();
                        rhsLinear = rhs.toLinear();
                    }
                } else {
                    if (lhsLinear.x instanceof LLVMHeuristicVariable && lhsLinear.x != null && rhsLinear.x != null) {
                        LLVMHeuristicState nextState =
                            res.handleMultiplicationCase(
                                shrinking,
                                replacements,
                                (LLVMHeuristicVariable)lhsLinear.x,
                                lhsLinear.y,
                                lhsLinear.z,
                                rhsLinear.y,
                                rhsLinear.z
                            );
                        if (!res.equals(nextState)) {
                            res = nextState;
                            curRel = curRel.applySubstitution(replacements);
                            lhs = curRel.getLhs();
                            rhs = curRel.getRhs();
                            lhsLinear = lhs.toLinear();
                            rhsLinear = rhs.toLinear();
                        }
                    }
                    if (rhsLinear.x instanceof LLVMHeuristicVariable && rhsLinear.x != null && lhsLinear.x != null) {
                        LLVMHeuristicState nextState =
                            res.handleMultiplicationCase(
                                shrinking,
                                replacements,
                                (LLVMHeuristicVariable)rhsLinear.x,
                                rhsLinear.y,
                                rhsLinear.z,
                                lhsLinear.y,
                                lhsLinear.z
                            );
                        if (!res.equals(nextState)) {
                            res = nextState;
                            curRel = curRel.applySubstitution(replacements);
                            lhs = curRel.getLhs();
                            rhs = curRel.getRhs();
                            lhsLinear = lhs.toLinear();
                            rhsLinear = rhs.toLinear();
                        }
                    }
                    if (
                        rhs.equals(this.getRelationFactory().getTermFactory().zero())
                        && lhs instanceof LLVMHeuristicOperation
                    ) {
                        LLVMHeuristicOperation op = (LLVMHeuristicOperation)lhs;
                        LLVMHeuristicTerm opLhs = null;
                        LLVMHeuristicTerm opRhs = null;
                        if (op.getOperation().equals(ArithmeticOperationType.ADD)) {
                            opLhs = op.getLhs();
                            opRhs = op.getRhs().negate();
                        } else if (op.getOperation().equals(ArithmeticOperationType.SUB)) {
                            opLhs = op.getLhs();
                            opRhs = op.getRhs();
                        }
                        if (opLhs != null && opRhs != null) {
                            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> opLhsLinear = opLhs.toLinear();
                            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> opRhsLinear = opRhs.toLinear();
                            if (
                                opLhsLinear.x instanceof LLVMHeuristicVariable
                                && opRhsLinear.x instanceof LLVMHeuristicVariable
                            ) {
                                LLVMHeuristicState nextState =
                                    res.handleMultiplicationCase(
                                        shrinking,
                                        replacements,
                                        (LLVMHeuristicVariable)opLhsLinear.x,
                                        opLhsLinear.y,
                                        opLhsLinear.z,
                                        (LLVMHeuristicVariable)opRhsLinear.x,
                                        opRhsLinear.y,
                                        opRhsLinear.z
                                    );
                                if (!res.equals(nextState)) {
                                    res = nextState;
                                    curRel = curRel.applySubstitution(replacements);
                                    lhs = curRel.getLhs();
                                    rhs = curRel.getRhs();
                                    lhsLinear = lhs.toLinear();
                                    rhsLinear = rhs.toLinear();
                                }
                            } else {
                                if (opLhsLinear.x instanceof LLVMHeuristicVariable && opRhsLinear.x != null) {
                                    LLVMHeuristicState nextState =
                                        res.handleMultiplicationCase(
                                            shrinking,
                                            replacements,
                                            (LLVMHeuristicVariable)opLhsLinear.x,
                                            opLhsLinear.y,
                                            opLhsLinear.z,
                                            opRhsLinear.y,
                                            opRhsLinear.z
                                        );
                                    if (!res.equals(nextState)) {
                                        res = nextState;
                                        curRel = curRel.applySubstitution(replacements);
                                        lhs = curRel.getLhs();
                                        rhs = curRel.getRhs();
                                        lhsLinear = lhs.toLinear();
                                        rhsLinear = rhs.toLinear();
                                    }
                                }
                                if (opRhsLinear.x instanceof LLVMHeuristicVariable &&
                                    opRhsLinear.x != null && opLhsLinear.x != null) {
                                    LLVMHeuristicState nextState =
                                        res.handleMultiplicationCase(
                                            shrinking,
                                            replacements,
                                            (LLVMHeuristicVariable)opRhsLinear.x,
                                            opRhsLinear.y,
                                            opRhsLinear.z,
                                            opLhsLinear.y,
                                            opLhsLinear.z
                                        );
                                    if (!res.equals(nextState)) {
                                        res = nextState;
                                        curRel = curRel.applySubstitution(replacements);
                                        lhs = curRel.getLhs();
                                        rhs = curRel.getRhs();
                                        lhsLinear = lhs.toLinear();
                                        rhsLinear = rhs.toLinear();
                                    }
                                }
                            }
                        }
                    }
                }
                LLVMHeuristicState nextState =
                    res.checkRemainderOperation(lhs, rhs, lhsLinear, rhsLinear, replacements, shrinking);
                if (!res.equals(nextState)) {
                    res = nextState;
                    curRel = curRel.applySubstitution(replacements);
                }
//                res = res.checkLimitRelation(curRel, replacements, shrinking, aborter);
                // no further replacements needed at the end, but think of it when adding more steps here
            }
            // check overflow modulo equalities
            final LLVMKnowledgeResult modEqResult = res.adjustValuesToModuloEquation(rel, shrinking, replacements, aborter);
            if (modEqResult != null) {
                return modEqResult;
            }
            // special case for multiplications in combination with pointer inequalities
            if (lhs instanceof LLVMHeuristicVarRef && rhs instanceof LLVMHeuristicOperation) {
                LLVMHeuristicOperation op = (LLVMHeuristicOperation)rhs;
                if (op.getOperation() == ArithmeticOperationType.ADD) {
                    LLVMHeuristicTerm opLhs = op.getLhs();
                    LLVMHeuristicTerm opRhs = op.getRhs();
                    if (opLhs instanceof LLVMHeuristicVarRef) {
                        res =
                            res.checkMultiplicationAndPointerInequalityCase(
                                (LLVMHeuristicVarRef)lhs,
                                (LLVMHeuristicVarRef)opLhs,
                                opRhs.toLinear(),
                                shrinking,
                                replacements,
                                aborter
                            );
                    } else if (opRhs instanceof LLVMHeuristicVarRef) {
                        res =
                            res.checkMultiplicationAndPointerInequalityCase(
                                (LLVMHeuristicVarRef)lhs,
                                (LLVMHeuristicVarRef)opRhs,
                                opLhs.toLinear(),
                                shrinking,
                                replacements,
                                aborter
                            );
                    }
                }
            }
            // check if we have two relations of the form x = a + y and x = a + z: then, y = z
            if (curRel.getNumberOfVarOccs() >= 2) {
                for (LLVMHeuristicRelation otherRel : res.getRelations()) {
                    if (otherRel.isEquation() && otherRel.getNumberOfVarOccs() >= 2) {
                        for (LLVMHeuristicVariable ref1 : curRel.getVariables(false)) {
                            for (LLVMHeuristicVariable ref2 : otherRel.getVariables(false)) {
                                if (!ref1.equals(ref2)
                                        && curRel.solveFor(ref1) != null
                                        && otherRel.solveFor(ref2) != null
                                        && curRel.solveFor(ref1).x.equals(otherRel.solveFor(ref2).x)) {
                                    LLVMHeuristicState restricted =
                                        res.restrictToUsedReferences(res.getValues().keySet(), aborter);
                                    LLVMReplacementResult repRes;
                                    if (restricted.getValue(ref2) != null) {
                                        repRes = res.unifySymbolicVariables(ref1, ref2);
                                    } else {
                                        repRes = res.unifySymbolicVariables(ref2, ref1);
                                    }
                                    LLVMHeuristicExpressionUtils.updateReplacements(replacements, repRes.y);
                                    shrinking.keySet().removeAll(replacements.keySet());
                                    res = repRes.x;
                                } else if (ref1.equals(ref2) && curRel.solveFor(ref1) != null && otherRel.solveFor(ref2) != null) {
                                    LLVMHeuristicTerm sub =
                                        (LLVMHeuristicTerm) res.getRelationFactory().getTermFactory().sub(
                                            curRel.solveFor(ref1).x,
                                            otherRel.solveFor(ref2).x
                                        );
                                    if (sub.isSumOfVariableAndConstant()) {
                                        LLVMHeuristicVarRef r = (LLVMHeuristicVarRef) sub.toLinear().x;
                                        BigInteger c = sub.toLinear().y.negate();
                                        LLVMReplacementResult repRes =
                                            res.unifySymbolicVariables(
                                                r,
                                                res.getRelationFactory().getTermFactory().constant(c)
                                            );
                                        LLVMHeuristicExpressionUtils.updateReplacements(replacements, repRes.y);
                                        shrinking.keySet().removeAll(replacements.keySet());
                                        res = repRes.x;
                                    }
                                }
                            }
                        }
                    }
                }
            }
            // check if we have two relations of the form x = c1 + y and x = c2 + z:
            // then, z = c1 - c2 + y and if v = c1 - c2 + y for another reference v, we have z = v.
            if (curRel.getLhs() instanceof LLVMHeuristicVarRef && curRel.getRhs().isSumOfVariableAndConstant()) {
                LLVMHeuristicVarRef x = (LLVMHeuristicVarRef) curRel.getLhs();
                BigInteger c1 = curRel.getRhs().toLinear().y;
                LLVMHeuristicVarRef y = (LLVMHeuristicVarRef) curRel.getRhs().toLinear().x;
                for (LLVMHeuristicRelation otherRel : res.getRelations()) {
                    if (otherRel.isEquation() && otherRel.getLhs().equals(x)
                            && otherRel.getRhs().isSumOfVariableAndConstant()
                            && !otherRel.getRhs().toLinear().y.equals(c1)) {
                        LLVMHeuristicVarRef z = (LLVMHeuristicVarRef) otherRel.getRhs().toLinear().x;
                        BigInteger c2 = otherRel.getRhs().toLinear().y;
                        BigInteger c1MinusC2 = c1.subtract(c2);
                        for (LLVMHeuristicRelation thirdRel : res.getRelations()) {
                            if (thirdRel.isEquation() && thirdRel.getLhs() instanceof LLVMHeuristicVarRef
                                    && thirdRel.getRhs().toLinear().x.equals(y)
                                    && thirdRel.getRhs().toLinear().y.compareTo(c1MinusC2) == 0
                                    && thirdRel.getRhs().toLinear().z.compareTo(BigInteger.ONE) == 0) {
                                LLVMHeuristicVarRef v = (LLVMHeuristicVarRef) thirdRel.getLhs();
                                LLVMReplacementResult repRes;
                                repRes = res.unifySymbolicVariables(v, z);
                                LLVMHeuristicExpressionUtils.updateReplacements(replacements, repRes.y);
                                shrinking.keySet().removeAll(replacements.keySet());
                                res = repRes.x;
                            }
                        }
                    }
                }
            }
        } else if (curRel.getHeuristicRelationType() == LLVMHeuristicRelationType.NE) {
            LLVMHeuristicTerm lhs = curRel.getLhs();
            LLVMHeuristicTerm rhs = curRel.getRhs();
            if (lhs instanceof LLVMHeuristicConstRef) {
                if (rhs instanceof LLVMHeuristicVarRef) {
                    LLVMReplacementResult repRes =
                        res.handleSimplePureInequality(
                            shrinking,
                            (LLVMHeuristicVariable)rhs,
                            ((LLVMHeuristicConstRef)lhs).getIntegerValue()
                        );
                    LLVMHeuristicExpressionUtils.updateReplacements(replacements, repRes.y);
                    shrinking.keySet().removeAll(replacements.keySet());
                    res = repRes.x;
                }
            } else if (rhs instanceof LLVMHeuristicConstRef) {
                if (lhs instanceof LLVMHeuristicVarRef) {
                    LLVMReplacementResult repRes =
                        res.handleSimplePureInequality(
                            shrinking,
                            (LLVMHeuristicVariable)lhs,
                            ((LLVMHeuristicConstRef)rhs).getIntegerValue()
                        );
                    LLVMHeuristicExpressionUtils.updateReplacements(replacements, repRes.y);
                    shrinking.keySet().removeAll(replacements.keySet());
                    res = repRes.x;
                }
            }
        } else {
            if (curRel.getHeuristicRelationType() == LLVMHeuristicRelationType.LT && curRel.isSimple()
                    && curRel.getLhs() instanceof LLVMHeuristicVarRef && curRel.getRhs() instanceof LLVMHeuristicVarRef) {
                // check if we have a relation x < y and equations
                // firstEq containing only variables x and z,
                // secondEq containing variables y and z,
                // and find equalities x = x_equiv_term and y = y_equiv_term,
                // then we can set x_equiv_term < y_equiv_term.
                LLVMHeuristicVarRef x = (LLVMHeuristicVarRef) curRel.getLhs();
                LLVMHeuristicVarRef y = (LLVMHeuristicVarRef) curRel.getRhs();
                for (LLVMHeuristicRelation firstEq : res.getRelations()) {
                    if (firstEq.isEquation() && firstEq.getVariables().contains(x) && firstEq.getNumberOfVarOccs() >= 2) {
                        LLVMHeuristicVarRef otherVar = null;
                        for (LLVMHeuristicVariable var : firstEq.getVariables()) {
                            if (var instanceof LLVMHeuristicVarRef && !var.equals(x)) {
                                otherVar = (LLVMHeuristicVarRef) var;
                            }
                        }
                        for (LLVMHeuristicRelation secondEq : res.getRelations()) {
                            if (secondEq.isEquation() && !secondEq.equals(firstEq) && secondEq.getVariables().contains(y)
                                && secondEq.getVariables().contains(otherVar) && secondEq.getNumberOfVarOccs() >= 2) {
                                Pair<LLVMHeuristicTerm, Boolean> x_equiv_term = firstEq.solveFor(x);
                                if (x_equiv_term != null) {
                                    Pair<LLVMHeuristicTerm, Boolean> y_equiv_term = secondEq.solveFor(y);
                                    if (y_equiv_term != null) {
                                        LLVMHeuristicRelation t1SmallerT2 =
                                                res.getRelationFactory().createRelation(IntegerRelationType.LT, x_equiv_term.x, y_equiv_term.x);
                                        LLVMHeuristicVarRef ref = (LLVMHeuristicVarRef) t1SmallerT2.getVariables(false).iterator().next();
                                        Pair<LLVMHeuristicTerm, Boolean> check = t1SmallerT2.solveFor(ref);
                                        if (check != null && check.x instanceof LLVMConstant) {
                                            BigInteger bound = ((LLVMConstant)check.x).getIntegerValue();
                                            LLVMValue value = this.getValue(ref);
                                            AbstractBoundedInt val = value.getThisAsAbstractBoundedInt();
                                            if (check.y) {
                                                IntervalBound lower = val.getLower();
                                                if (!lower.isFinite() || lower.getConstant().compareTo(bound) < 0) {
                                                    shrinking.put(ref, new Pair<BigInteger, BigInteger>(bound, null));
                                                    LLVMValue nextVal = val.setLower(IntervalBound.create(bound));
                                                    return new LLVMKnowledgeResult(this.setValue(ref, nextVal), shrinking, replacements);
                                                }
                                            } else {
                                                IntervalBound upper = val.getUpper();
                                                if (!upper.isFinite() || upper.getConstant().compareTo(bound) > 0) {
                                                    shrinking.put(ref, new Pair<BigInteger, BigInteger>(null, bound));
                                                    LLVMValue nextVal = val.setUpper(IntervalBound.create(bound));
                                                    return new LLVMKnowledgeResult(this.setValue(ref, nextVal), shrinking, replacements);
                                                }
                                            }
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
            // check overflow modulo inequalities
            final LLVMKnowledgeResult modIneqResult = res.adjustValuesToInnerBoundRelation(rel, shrinking, replacements);
            if (modIneqResult != null) {
                return modIneqResult;
            }
        }
        return new LLVMKnowledgeResult(res, shrinking, replacements);
    }

    private LLVMKnowledgeResult adjustValuesToInnerBoundRelation(
        LLVMHeuristicRelation rel,
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> shrinking,
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements
    ) {
        final LLVMHeuristicTermFactory termFactory = this.getRelationFactory().getTermFactory();
        LLVMHeuristicState res = this;
        if (
            rel.getHeuristicRelationType() == LLVMHeuristicRelationType.LE
            && rel.getLhs() instanceof LLVMHeuristicOperation
            && rel.getRhs() instanceof LLVMHeuristicConstRef
        ) {
            LLVMHeuristicOperation lhs = (LLVMHeuristicOperation) rel.getLhs();
            if (
                lhs.getOperation() != ArithmeticOperationType.EMOD || !(lhs.getRhs() instanceof LLVMHeuristicConstRef)
            ) {
                return null;
            }
            // we have a relation of the form expr1 mod c1 <= c2, where c1 and c2 are constants
            // try to match the relation with (ref + offset) mod c1 <= c2
            LLVMHeuristicVariable ref;
            LLVMHeuristicConstRef offset;
            if (lhs.getLhs() instanceof LLVMHeuristicVarRef) {
                // we have a relation of the form ref (+ 0) mod c1 <= c2, where offset, c1 and c2 are constants
                ref = (LLVMHeuristicVariable)lhs.getLhs();
                offset = termFactory.zero();
            } else if (lhs.getLhs() instanceof LLVMHeuristicOperation) {
                LLVMHeuristicOperation lhsOfLhs = (LLVMHeuristicOperation)lhs.getLhs();
                // try to match the relation with (ref + offset) mod c1 <= c2
                if (
                    lhsOfLhs.getLhs() instanceof LLVMHeuristicVarRef
                    && lhsOfLhs.getRhs() instanceof LLVMHeuristicConstRef
                ) {
                    ref = (LLVMHeuristicVariable)lhsOfLhs.getLhs();
                    if (lhsOfLhs.getOperation().equals(ArithmeticOperationType.ADD)) {
                        offset = (LLVMHeuristicConstRef)lhsOfLhs.getRhs();
                    } else if (lhsOfLhs.getOperation().equals(ArithmeticOperationType.SUB)) {
                        offset = (LLVMHeuristicConstRef)lhsOfLhs.getRhs().negate();
                    } else {
                        return null;
                    }
                } else if (
                    lhsOfLhs.getLhs() instanceof LLVMHeuristicConstRef
                    && lhsOfLhs.getRhs() instanceof LLVMHeuristicVarRef
                ) {
                    ref = (LLVMHeuristicVariable)lhsOfLhs.getRhs();
                    if (lhsOfLhs.getOperation().equals(ArithmeticOperationType.ADD)) {
                        offset = (LLVMHeuristicConstRef)lhsOfLhs.getLhs();
                    } else {
                        return null;
                    }
                } else {
                    return null;
                }
            } else {
                return null;
            }
            // we have a relation of the form (ref + offset) mod c1 <= c2, where offset, c1 and c2 are constants
            AbstractBoundedInt valOfRef = this.getValue(ref).getThisAsAbstractBoundedInt();
            BigInteger valOfC1 = ((LLVMHeuristicConstRef) lhs.getRhs()).getIntegerValue();
            LLVMHeuristicConstRef c2 = (LLVMHeuristicConstRef) rel.getRhs();
            BigInteger valOfC2 = c2.getIntegerValue();
            BigInteger valOfOffset = offset.getIntegerValue();
            BigInteger refLB = valOfRef.getLower().getConstant();
            BigInteger refUB = valOfRef.getUpper().getConstant();
            if (
                (
                    refLB.compareTo(BigInteger.ZERO) >= 0
                    || refLB.multiply(BigInteger.valueOf(-2)).compareTo(valOfC1) <= 0
                ) && (
                    refUB.compareTo(BigInteger.ZERO) <= 0
                    || refUB.add(BigInteger.ONE).multiply(BigInteger.valueOf(2)).compareTo(valOfC1) <= 0
                )
            ) {
                // we have an inner bound relation -> compute inner bounds:
                // ((ref + offset) mod c1 <= c2) implies (ref <= c2 - offset - c1) or (ref >= -offset)
                BigInteger innerUB = valOfC2.subtract(valOfOffset).subtract(valOfC1);
                BigInteger innerLB = valOfOffset.negate();
                // a) if we know (ref > c2 - offset - c1), we imply (ref >= -offset)
                if (refLB.compareTo(innerUB) > 0 && refLB.compareTo(innerLB) < 0) {
                    if (Globals.useAssertions) {
                        assert (refUB.compareTo(innerLB) >= 0) : "Inconsistent state detected!";
                    }
                    final AbstractBoundedInt newVal = valOfRef.setLower(IntervalBound.create(innerLB));
                    if(newVal == null) {
                    	throw new InconsistentStateException(null, null);
                    }
                    // check if we have a constant value now
                    if (newVal.isIntLiteral()) {
                        // restrict ref to a constant
                        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> newReplacements =
                            new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>();
                        newReplacements.put(ref, termFactory.constant(newVal.getIntLiteralValue()));
                        LLVMHeuristicExpressionUtils.updateReplacements(replacements, newReplacements);
                        res = res.replaceSymbolicVariable(ref, termFactory.constant(newVal.getIntLiteralValue()));
                        shrinking.keySet().removeAll(replacements.keySet());
                    } else {
                        // restrict ref to an interval with a new lower bound
                        res = res.setValue(ref, newVal);
                        shrinking.put(ref, new Pair<BigInteger, BigInteger>(innerLB, refUB));
                    }
                    return new LLVMKnowledgeResult(res, shrinking, replacements);
                }
                // b) if we know (ref < -offset), we imply (ref <= c2 - offset - c1)
                if (refUB.compareTo(innerLB) < 0 && refUB.compareTo(innerUB) > 0) {
                    if (Globals.useAssertions) {
                        assert (refLB.compareTo(innerUB) <= 0) : "Inconsistent state detected!";
                    }
                    final AbstractBoundedInt newVal = valOfRef.setUpper(IntervalBound.create(innerUB));
                    if(newVal == null) {
                    	throw new InconsistentStateException(null, null);
                    }
                    // check if we have a constant value now
                    if (newVal.isIntLiteral()) {
                        // restrict ref to a constant
                        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> newReplacements =
                            new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>();
                        newReplacements.put(ref, termFactory.constant(newVal.getIntLiteralValue()));
                        LLVMHeuristicExpressionUtils.updateReplacements(replacements, newReplacements);
                        res = res.replaceSymbolicVariable(ref, termFactory.constant(newVal.getIntLiteralValue()));
                        shrinking.keySet().removeAll(replacements.keySet());
                    } else {
                        // restrict ref to an interval with a new upper bound
                        res = res.setValue(ref, newVal);
                        shrinking.put(ref, new Pair<BigInteger, BigInteger>(refLB, innerUB));
                    }
                    return new LLVMKnowledgeResult(res, shrinking, replacements);
                }
            }
        }
        return null;
    }

    private LLVMKnowledgeResult adjustValuesToModuloEquation(
        LLVMHeuristicRelation rel,
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> shrinking,
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements,
        Abortion aborter
    ) {
        LLVMHeuristicState res = this;
        LLVMHeuristicTerm lhs = rel.getLhs();
        LLVMHeuristicTerm rhs = rel.getRhs();
        if (
            rhs instanceof LLVMHeuristicOperation
            && ((LLVMHeuristicOperation)rhs).getOperation() == ArithmeticOperationType.EMOD
        ) {
            if (lhs.getNumberOfVarOccs() == 1 && rhs.getNumberOfVarOccs() == 1) {
                // determine the references
                LLVMHeuristicVariable refLhs = null;
                LLVMHeuristicVariable refRhs = null;
                Iterator<? extends LLVMHeuristicVariable> refItLhs = lhs.getVariables().iterator();
                while (refItLhs.hasNext()) {
                    refLhs = refItLhs.next();
                    if (refLhs instanceof LLVMHeuristicVarRef) {
                        break;
                    }
                }
                Iterator<? extends LLVMHeuristicVariable> refItRhs = rhs.getVariables().iterator();
                while (refItRhs.hasNext()) {
                    refRhs = refItRhs.next();
                    if (refRhs instanceof LLVMHeuristicVarRef) {
                        break;
                    }
                }
                // for the extremal values of refRHS, calculate the outcome of refLHS
                Pair<LLVMHeuristicTerm, Boolean> refLhsNewLower = null;
                Pair<LLVMHeuristicTerm, Boolean> refLhsNewUpper = null;
                LLVMHeuristicConstRef rhsLowerBound = null;
                LLVMHeuristicConstRef rhsUpperBound = null;
                BigInteger refRhsLower = this.getValue(refRhs).getThisAsAbstractBoundedInt().getLower().getConstant();
                BigInteger refRhsUpper = this.getValue(refRhs).getThisAsAbstractBoundedInt().getUpper().getConstant();
                LiteralBoundedInt refRhsLowerLit = AbstractBoundedInt.create(refRhsLower);
                LiteralBoundedInt refRhsUpperLit = AbstractBoundedInt.create(refRhsUpper);
                HashMap<LLVMHeuristicVariable,LLVMValue> mapRhsLower = new HashMap<LLVMHeuristicVariable,LLVMValue>();
                HashMap<LLVMHeuristicVariable,LLVMValue> mapRhsUpper = new HashMap<LLVMHeuristicVariable,LLVMValue>();
                mapRhsLower.put(refRhs, refRhsLowerLit);
                mapRhsUpper.put(refRhs, refRhsUpperLit);
                final LLVMHeuristicTermFactory termFactory = this.getRelationFactory().getTermFactory();
                try {
                    rhsLowerBound =
                        termFactory.constant(
                            rhs.evaluate(mapRhsLower, this.getStrategyParamters()).getIntLiteralValue()
                        );
                    rhsUpperBound =
                        termFactory.constant(
                            rhs.evaluate(mapRhsUpper, this.getStrategyParamters()).getIntLiteralValue()
                        );
                    LLVMHeuristicRelation relForLhsLower =
                        this.getRelationFactory().createRelation(IntegerRelationType.EQ, lhs, rhsLowerBound);
                    LLVMHeuristicRelation relForLhsUpper =
                        this.getRelationFactory().createRelation(IntegerRelationType.EQ, lhs, rhsUpperBound);
                    // for refLHS, calculate the lower and the upper bound resulting from this equation
                    refLhsNewLower = relForLhsLower.solveFor(refLhs);
                    refLhsNewUpper = relForLhsUpper.solveFor(refLhs);
                    // Now check if we can restrict the interval of refLHS.
                    // For example, if refLhs = [0,MaxInt] and the equation tells us
                    // refLhs >= 10 or refLhs <= MinInt, then the new interval is [10, MaxInt].
                    BigInteger refLhsLowerBoundFromInterval =
                        this.getValue(refLhs).getThisAsAbstractBoundedInt().getLower().getConstant();
                    BigInteger refLhsUpperBoundFromInterval =
                        this.getValue(refLhs).getThisAsAbstractBoundedInt().getUpper().getConstant();
                    BigInteger refLhsLowerBoundFromRelation =
                        ((LLVMHeuristicConstRef)refLhsNewLower.x).getIntegerValue();
                    BigInteger refLhsUpperBoundFromRelation =
                        ((LLVMHeuristicConstRef)refLhsNewUpper.x).getIntegerValue();
                    IntervalBound refLhsFinalLower = null;
                    IntervalBound refLhsFinalUpper = null;
                    AbstractBoundedInt refLhsOldVal = this.getValue(refLhs).getThisAsAbstractBoundedInt();
                    // restrict the interval of refLHS
                    if (refLhsLowerBoundFromRelation.compareTo(refLhsUpperBoundFromRelation) > 0) {
                        // should be the normal case (such relations are only added if overflow possible)
                        if (refLhsUpperBoundFromInterval.compareTo(refLhsLowerBoundFromRelation) < 0 &&
                            refLhsUpperBoundFromInterval.compareTo(refLhsUpperBoundFromRelation) > 0) {
                            // we can restrict the interval by a new upper bound
                            assert (refLhsUpperBoundFromRelation.compareTo(refLhsLowerBoundFromInterval) >= 0) :
                                "Inconsistent state detected: Value not consistent with modulo relation!";
                            refLhsFinalLower = refLhsOldVal.getLower();
                            // the new upper bound is the upper bound extracted from the relation
                            refLhsFinalUpper = IntervalBound.create(refLhsUpperBoundFromRelation);
                        }
                        if (refLhsLowerBoundFromInterval.compareTo(refLhsLowerBoundFromRelation) < 0 &&
                            refLhsLowerBoundFromInterval.compareTo(refLhsUpperBoundFromRelation) > 0) {
                            // we can restrict the interval by a new lower bound
                            assert (refLhsLowerBoundFromRelation.compareTo(refLhsUpperBoundFromInterval) <= 0) :
                                "Inconsistent state detected: Value not consistent with modulo relation!";
                            // the new lower bound is the lower bound extracted from the relation
                            refLhsFinalLower = IntervalBound.create(refLhsLowerBoundFromRelation);
                            refLhsFinalUpper = refLhsOldVal.getUpper();
                        }
                    }
                    if (refLhsFinalLower == null || refLhsFinalUpper == null) {
                        LLVMHeuristicTerm rhsOfRhs =  ((LLVMHeuristicOperation)rhs).getRhs();
                        if (rhsOfRhs instanceof LLVMHeuristicConstRef) {
                            // we have a relation expr1 = expr2 mod c
                            // TODO if expr1 may be < 0 or > c, restrict the reference of expr1 (needed?)
                        }
                    }
                    if (refLhsFinalLower != null && refLhsFinalUpper != null) {
                        // restrict the interval by new bounds
                        if (refLhsFinalLower.equals(refLhsFinalUpper)) {
                            Map<LLVMHeuristicVariable, LLVMHeuristicVariable> newReplacements =
                                new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>();
                            newReplacements.put(refLhs, termFactory.constant(refLhsFinalLower.getConstant()));
                            LLVMHeuristicExpressionUtils.updateReplacements(replacements, newReplacements);
                            res =
                                res.replaceSymbolicVariable(
                                    refLhs,
                                    termFactory.constant(refLhsFinalLower.getConstant())
                                );
                            shrinking.keySet().removeAll(replacements.keySet());
                        } else {
                            AbstractBoundedInt newVal =
                                AbstractBoundedInt.create(
                                    refLhsFinalLower,
                                    refLhsFinalUpper,
                                    refLhsOldVal.getMinLower(),
                                    refLhsOldVal.getMaxUpper(),
                                    refLhsOldVal.getLowerCounter(),
                                    refLhsOldVal.getUpperCounter()
                                );

                            // set refLHS to the new value
                            res = res.setValue(refLhs, newVal);
                            shrinking.put(
                                refLhs,
                                new Pair<BigInteger, BigInteger>(
                                    refLhsFinalLower.getConstant(),
                                    refLhsFinalUpper.getConstant()
                                )
                            );
                        }
                        return new LLVMKnowledgeResult(res, shrinking, replacements);
                    }
                } catch (AbstractBoundedInt.OverflowException e) {
                    throw new IllegalStateException(
                        "Overflow in relation could not be handled correctly!"
                    );
                }
                // for the extremal values of refLHS, calculate the outcome of refRHS
                Pair<LLVMHeuristicTerm, Boolean> refRhsNewLower = null;
                Pair<LLVMHeuristicTerm, Boolean> refRhsNewUpper = null;
                LLVMHeuristicConstRef lhsLowerBound = null;
                LLVMHeuristicConstRef lhsUpperBound = null;
                BigInteger refLhsLower = this.getValue(refLhs).getThisAsAbstractBoundedInt().getLower().getConstant();
                BigInteger refLhsUpper = this.getValue(refLhs).getThisAsAbstractBoundedInt().getUpper().getConstant();
                LiteralBoundedInt refLhsLowerLit = AbstractBoundedInt.create(refLhsLower);
                LiteralBoundedInt refLhsUpperLit = AbstractBoundedInt.create(refLhsUpper);
                HashMap<LLVMHeuristicVariable,LLVMValue> mapLhsLower = new HashMap<LLVMHeuristicVariable,LLVMValue>();
                HashMap<LLVMHeuristicVariable,LLVMValue> mapLhsUpper = new HashMap<LLVMHeuristicVariable,LLVMValue>();
                mapLhsLower.put(refLhs, refLhsLowerLit);
                mapLhsUpper.put(refLhs, refLhsUpperLit);
                try {
                    lhsLowerBound =
                        termFactory.constant(
                            lhs.evaluate(mapLhsLower, this.getStrategyParamters()).getIntLiteralValue()
                        );
                    lhsUpperBound =
                        termFactory.constant(
                            lhs.evaluate(mapLhsUpper, this.getStrategyParamters()).getIntLiteralValue()
                        );
                    LLVMHeuristicRelation relForRhsLower =
                        this.getRelationFactory().createRelation(IntegerRelationType.EQ, lhsLowerBound, rhs);
                    LLVMHeuristicRelation relForRhsUpper =
                        this.getRelationFactory().createRelation(IntegerRelationType.EQ, lhsUpperBound, rhs);
                    // for refRHS, calculate the lower and the upper bound resulting from this equation
                    refRhsNewLower = relForRhsLower.solveModuloNormalForm(refRhs, this.getValue(refRhs));
                    refRhsNewUpper = relForRhsUpper.solveModuloNormalForm(refRhs, this.getValue(refRhs));
                    if (refRhsNewLower == null || refRhsNewUpper == null) {
                        return null;
                    }
                    // Now check if we can restrict the interval of refRHS.
                    BigInteger refRhsLowerBoundFromInterval =
                        this.getValue(refRhs).getThisAsAbstractBoundedInt().getLower().getConstant();
                    BigInteger refRhsUpperBoundFromInterval =
                        this.getValue(refRhs).getThisAsAbstractBoundedInt().getUpper().getConstant();
                    BigInteger refRhsLowerBoundFromRelation =
                        ((LLVMHeuristicConstRef)refRhsNewLower.x).getIntegerValue();
                    BigInteger refRhsUpperBoundFromRelation =
                        ((LLVMHeuristicConstRef)refRhsNewUpper.x).getIntegerValue();
                    IntervalBound refRhsFinalLower = null;
                    IntervalBound refRhsFinalUpper = null;
                    AbstractBoundedInt refRhsOldVal = this.getValue(refRhs).getThisAsAbstractBoundedInt();
                    // restrict the interval of refRHS
                    if (refRhsLowerBoundFromRelation.compareTo(refRhsUpperBoundFromRelation) < 0) {
                        if (refRhsLowerBoundFromRelation.compareTo(refRhsLowerBoundFromInterval) > 0) {
                            // we can restrict the interval by a new lower bound
                            assert (refRhsLowerBoundFromRelation.compareTo(refRhsUpperBoundFromInterval) <= 0) :
                                "Inconsistent state detected: Value not consistent with modulo relation!";
                            // the new lower bound is the lower bound extracted from the relation
                            refRhsFinalLower = IntervalBound.create(refRhsLowerBoundFromRelation);
                            refRhsFinalUpper = refRhsOldVal.getUpper();
                        }
                        if (refRhsUpperBoundFromRelation.compareTo(refRhsUpperBoundFromInterval) < 0) {
                            // we can restrict the interval by a new lower bound
                            assert (refRhsUpperBoundFromRelation.compareTo(refRhsLowerBoundFromInterval) > 0) :
                                "Inconsistent state detected: Value not consistent with modulo relation!";
                            // only set lower bound if the lower bound has not been adapted yet
                            if (refRhsFinalLower == null) {
                                refRhsFinalLower = refRhsOldVal.getLower();
                            }
                            // the new upper bound is the upper bound extracted from the relation
                            refRhsFinalUpper = IntervalBound.create(refRhsUpperBoundFromRelation);
                        }
                        if (refRhsFinalLower != null && refRhsFinalUpper != null) {
                            // restrict the interval by new bounds
                            if (refRhsFinalLower.equals(refRhsFinalUpper)) {
                                Map<LLVMHeuristicVariable, LLVMHeuristicVariable> newReplacements =
                                    new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>();
                                newReplacements.put(refRhs, termFactory.constant(refRhsFinalLower.getConstant()));
                                LLVMHeuristicExpressionUtils.updateReplacements(replacements, newReplacements);
                                res =
                                    res.replaceSymbolicVariable(
                                        refRhs,
                                        termFactory.constant(refRhsFinalLower.getConstant())
                                    );
                                shrinking.keySet().removeAll(replacements.keySet());
                            } else {
                                final AbstractBoundedInt newVal =
                                    AbstractBoundedInt.create(
                                        refRhsFinalLower,
                                        refRhsFinalUpper,
                                        refRhsOldVal.getMinLower(),
                                        refRhsOldVal.getMaxUpper(),
                                        refRhsOldVal.getLowerCounter(),
                                        refRhsOldVal.getUpperCounter()
                                    );
                                // set refRHS to the new value
                                res = res.setValue(refRhs, newVal);
                                shrinking.put(
                                    refRhs,
                                    new Pair<BigInteger, BigInteger>(
                                        refRhsFinalLower.getConstant(),
                                        refRhsFinalUpper.getConstant()
                                    )
                                );
                            }
                            return new LLVMKnowledgeResult(res, shrinking, replacements);
                        }
                    }
                } catch (AbstractBoundedInt.OverflowException e) {
                    throw new IllegalStateException(
                        "Overflow in relation could not be handled correctly!"
                    );
                }
            }
        } else if (
            rhs instanceof LLVMHeuristicOperation
            && ((LLVMHeuristicOperation)rhs).getOperation() == ArithmeticOperationType.TMOD
        ) {
            LLVMHeuristicOperation modOp = (LLVMHeuristicOperation) rhs;
            if (modOp.isSimple()) {
                if (lhs instanceof LLVMHeuristicVarRef
                    && this.checkIfNonNegative(modOp.getLhs(), aborter).x
                    && this.checkIfPositive(modOp.getRhs(), aborter).x) {
                    // Now check if we can restrict the interval of lhs.
                    LLVMHeuristicVarRef ref = (LLVMHeuristicVarRef) lhs;
                    if (this.getValue(ref) == null) {
                        return null;
                    }
                    final AbstractBoundedInt oldVal = this.getValue(ref).getThisAsAbstractBoundedInt();
                    if (oldVal.getLower().isNegative()) {
                        final AbstractBoundedInt newVal =
                            AbstractBoundedInt.create(
                                IntervalBound.ZERO,
                                oldVal.getUpper(),
                                oldVal.getMinLower(),
                                oldVal.getMaxUpper(),
                                oldVal.getLowerCounter(),
                                oldVal.getUpperCounter()
                            );
                        // set ref to the new value
                        res = res.setValue(ref, newVal);
                        BigInteger upper = null;
                        if (oldVal.getUpper().isFinite()) {
                            upper = oldVal.getUpper().getConstant();
                        }
                        shrinking.put(ref, new Pair<BigInteger, BigInteger>(BigInteger.ZERO, upper));
                        return new LLVMKnowledgeResult(res, shrinking, replacements);
                    }
                }
            }
        }
        return null;
    }

    private LLVMKnowledgeResult adjustValuesToStructInvariant(
        LLVMMemoryRecursiveRange range,
        LLVMCombinedMemoryInvariant combInv,
        Abortion aborter
    ) {
        LLVMHeuristicState res = this;
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> shrinking =
            new LinkedHashMap<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>>();
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements =
            new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>();
        if (!(range.getLength() instanceof LLVMHeuristicVariable)) {
            return new LLVMKnowledgeResult(res, shrinking, replacements);
        }
        LLVMHeuristicVariable lengthRef = (LLVMHeuristicVariable) range.getLength();
        LLVMValue lengthValue = res.getValue(lengthRef);
        if (lengthValue == null) {
            return new LLVMKnowledgeResult(res, shrinking, replacements);
        }
        AbstractBoundedInt lengthVal = lengthValue.getThisAsAbstractBoundedInt();
        IntervalBound lengthLower = lengthVal.getLower();
        BigInteger newLengthLower = null;
        if (lengthLower.isFinite()) {
            newLengthLower = lengthLower.getConstant();
        }
        // invariants => length:
        // if there is a complex invariant (v..0;-1) with v >= 2, a lower bound for the length is 3
        for (LLVMMemoryInvariant inv : combInv.getInvariants().values()) {
            if (inv instanceof LLVMComplexMemoryInvariant) {
                LLVMComplexMemoryInvariant compInv = (LLVMComplexMemoryInvariant) inv;
                if (compInv.getFirstValue() == null) {
                    continue;
                }
                if (compInv.getLastValue() == null) {
                    continue;
                }
                LLVMValue firstValue = res.getValue((LLVMHeuristicVariable)compInv.getFirstValue());
                if (firstValue == null) {
                    continue;
                }
                AbstractBoundedInt firstVal = firstValue.getThisAsAbstractBoundedInt();
                IntervalBound firstLower = firstVal.getLower();
                if (!firstLower.isFinite()) {
                    // if there is a complex invariant (v..u;?) with v != u, a lower bound for the length is 2
                    if (res.checkRelation(compInv.getFirstValue(), IntegerRelationType.NE, compInv.getLastValue(), aborter).x) {
                        newLengthLower = BigInteger.TWO;
                    } else {
                        continue;
                    }
                } else {
                    BigInteger invLength = compInv.deduceLowerBoundForLength(firstLower.getConstant());
                    if (newLengthLower == null || invLength.compareTo(newLengthLower) > 0) {
                        newLengthLower = invLength;
                    } else {
                        if (res.checkRelation(compInv.getFirstValue(), IntegerRelationType.NE, compInv.getLastValue(), aborter).x) {
                            newLengthLower = BigInteger.TWO;
                        }
                    }
                }
            }
        }
        LLVMHeuristicVariable lastPtr = (LLVMHeuristicVariable) combInv.getLastRecursivePointer();
        if (newLengthLower == null) {
            return new LLVMKnowledgeResult(res, shrinking, replacements);
        }
        LLVMHeuristicVariable startRef = (LLVMHeuristicVariable) range.getFromRef();
        if (newLengthLower.compareTo(BigInteger.ONE) < 0) {
            // if startRef != lastPtr, we have length > 0
            if (res.checkRelation(startRef, IntegerRelationType.NE, lastPtr, aborter).x) {
                newLengthLower = BigInteger.ONE;
            }
        }
        LLVMHeuristicTermFactory termFactory = res.getRelationFactory().getTermFactory();
        // if startRef = 0, we have length = 0 and lastRef = 0
        if (startRef.equals(termFactory.zero())) {
            if (lengthRef instanceof LLVMHeuristicVarRef) {
                replacements.put(lengthRef, termFactory.zero());
                res = res.replaceSymbolicVariable(lengthRef, termFactory.zero());
                shrinking.remove(lengthRef);
            }
            if (lastPtr instanceof LLVMHeuristicVarRef) {
                replacements.put(lastPtr, termFactory.zero());
                res = res.replaceSymbolicVariable(lastPtr, termFactory.zero());
                shrinking.remove(lastPtr);
            }
        }
        // TODO if startRef = lastRef, we have length = 0
        if (lengthLower.compareTo(newLengthLower) < 0) {
            shrinking.put(lengthRef, new Pair<BigInteger, BigInteger>(newLengthLower, null));
            LLVMValue nextLength = lengthVal.setLower(IntervalBound.create(newLengthLower));
            if(nextLength == null) {
                throw new InconsistentStateException(null, null);
            }
            res = res.setValue(lengthRef, nextLength);
        }
        // length => invariants:
        // if there is a complex invariant (v..0;-1) of length >= 3, a lower bound for v is 2
        for (LLVMMemoryInvariant inv : combInv.getInvariants().values()) {
            if (inv instanceof LLVMComplexMemoryInvariant) {
                LLVMComplexMemoryInvariant compInv = (LLVMComplexMemoryInvariant) inv;
                LLVMHeuristicVariable firstRef = (LLVMHeuristicVariable) compInv.getFirstValue();
                if (firstRef == null) {
                    continue;
                }
                LLVMValue firstValue = res.getValue(firstRef);
                if (firstValue == null) {
                    continue;
                }
                AbstractBoundedInt firstVal = firstValue.getThisAsAbstractBoundedInt();
                IntervalBound firstLower = firstVal.getLower();
                IntervalBound firstUpper = firstVal.getUpper();
                BigInteger newFirstLower = compInv.deduceLowerBoundForFirst(newLengthLower);
                if (newFirstLower != null && firstLower.compareTo(newFirstLower) < 0) {
                    shrinking.put(firstRef, new Pair<BigInteger, BigInteger>(newFirstLower, null));
                    LLVMValue nextFirst = firstVal.setLower(IntervalBound.create(newFirstLower));
                    if(nextFirst == null) {
                        throw new InconsistentStateException(null, null);
                    }
                    res = res.setValue(firstRef, nextFirst);
                }
                BigInteger newFirstUpper = compInv.deduceUpperBoundForFirst(newLengthLower);
                if (newFirstUpper != null && firstUpper.compareTo(newFirstUpper) > 0) {
                    shrinking.put(firstRef, new Pair<BigInteger, BigInteger>(null, newFirstUpper));
                    LLVMValue nextFirst = firstVal.setUpper(IntervalBound.create(newFirstUpper));
                    if(nextFirst == null) {
                        throw new InconsistentStateException(null, null);
                    }
                    res = res.setValue(firstRef, nextFirst);
                }
            }
        }
        // if length > 0, we have startRef > 0
        LLVMHeuristicVariable length = (LLVMHeuristicVariable) range.getLength();
        LLVMValue startRefValue = res.getValue(startRef);
        if (startRefValue == null) {
            return new LLVMKnowledgeResult(res, shrinking, replacements);
        }
        AbstractBoundedInt startRefVal = startRefValue.getThisAsAbstractBoundedInt();
        IntervalBound startRefLower = startRefVal.getLower();
        BigInteger newStartRefLower = null;
        if (res.checkIfPositive(length, aborter).x) {
            newStartRefLower = BigInteger.ONE;
        }
        if (newStartRefLower != null && startRefLower.compareTo(newStartRefLower) < 0) {
            shrinking.put(startRef, new Pair<BigInteger, BigInteger>(newStartRefLower, null));
            LLVMValue nextStartRef = lengthVal.setLower(IntervalBound.create(newLengthLower));
            if(nextStartRef == null) {
                throw new InconsistentStateException(null, null);
            }
            res = res.setValue(startRef, nextStartRef);
        }
        // TODO if length = 0, we have startRef = lastRef
        return new LLVMKnowledgeResult(res, shrinking, replacements);
    }

    /**
     * @param unassociatedRef The reference which might be associated.
     * @param index The reference possibly used as index (must be non-negative).
     * @param limit The constant upper limit of the index.
     * @param alloc The allocation to which unassociatedRef might be associated.
     * @param allocIndex The index of the allocation.
     * @param expr An expression known to be equal to unassociatedRef - alloc.x.
     * @param unassociatedPointerRefs The yet unassociated references.
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @return The state emerging from this state by adding a further association based on the knowledge that index has
     *         decreased its value and expr is of the form index * c for some non-negative constant c such that
     *         limit * c + off <= alloc.y - alloc.x holds for off being the association offset of unassociatedRef.
     */
    private LLVMHeuristicState checkArrayIndexForFurtherAssociation(
        LLVMHeuristicVariable unassociatedRef,
        LLVMHeuristicVariable index,
        BigInteger limit,
        LLVMAllocation alloc,
        int allocIndex,
        LLVMHeuristicTerm expr,
        Map<LLVMHeuristicVariable, TreeSet<LLVMPointerType>> unassociatedPointerRefs,
        Set<LLVMRelation> newRels,
        Abortion aborter
    ) {
        BigInteger offset;
        if (expr instanceof LLVMHeuristicOperation) {
            LLVMHeuristicOperation op = (LLVMHeuristicOperation)expr;
            if (op.getOperation() != ArithmeticOperationType.MUL) {
                return this;
            }
            LLVMHeuristicTerm opLhs = op.getLhs();
            LLVMHeuristicTerm opRhs = op.getRhs();
            if (opLhs.equals(index)) {
                if (opRhs instanceof LLVMHeuristicConstRef) {
                    offset = ((LLVMHeuristicConstRef)opRhs).getIntegerValue();
                } else {
                    return this;
                }
            } else if (opRhs.equals(index)) {
                if (opLhs instanceof LLVMHeuristicConstRef) {
                    offset = ((LLVMHeuristicConstRef)opLhs).getIntegerValue();
                } else {
                    return this;
                }
            } else {
                return this;
            }
        } else if (expr.equals(index)) {
            offset = BigInteger.ONE;
        } else {
            return this;
        }
        offset = offset.multiply(limit);
        if (offset.compareTo(BigInteger.ZERO) < 0) {
            return this;
        }
        Iterator<LLVMPointerType> it = unassociatedPointerRefs.get(unassociatedRef).descendingIterator();
        final LLVMHeuristicRelationFactory relationFactory = this.getRelationFactory();
        final LLVMHeuristicTermFactory termFactory = relationFactory.getTermFactory();
        LLVMHeuristicState res = this;
        while (it.hasNext()) {
            LLVMPointerType type = it.next();
            final Pair<Boolean, ? extends LLVMAbstractState> check =
                res.checkRelation(
                    relationFactory.lessThanEquals(
                        termFactory.create(
                            ArithmeticOperationType.ADD,
                            (LLVMHeuristicVariable)alloc.x,
                            termFactory.constant(offset.add(type.toOffset()))
                        ),
                        alloc.y
                    ),
                    aborter
                );
            res = (LLVMHeuristicState)check.y;
            if (check.x) {
                return res.associateAccess(unassociatedRef, type, allocIndex, newRels, aborter);
            }
        }
        return res;
    }

    /**
     * @param unassociatedRef The reference which might be associated.
     * @param index The reference possibly used as index (must be non-negative).
     * @param limit The constant upper limit of the index.
     * @param expr The expression being equal to the unassociated reference.
     * @param unassociatedPointerRefs The yet unassociated references.
     * @param allocs The allocations.
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @return The state emerging from this state by adding a further association based on the knowledge that index has
     *         decreased its value and expr is of the form lower + index * c for some lower allocation limit lower and
     *         some non-negative constant c such that limit * c + offset <= upper - lower holds for upper being the
     *         upper allocation limit and offset being the association offset of unassociatedRef.
     */
    private LLVMHeuristicState checkArrayIndexForFurtherAssociation(
        LLVMHeuristicVariable unassociatedRef,
        LLVMHeuristicVariable index,
        BigInteger limit,
        LLVMHeuristicTerm expr,
        Map<LLVMHeuristicVariable, TreeSet<LLVMPointerType>> unassociatedPointerRefs,
        ImmutableList<LLVMAllocation> allocs,
        Set<LLVMRelation> newRels,
        Abortion aborter
    ) {
        if (!(expr instanceof LLVMHeuristicOperation)) {
            return this;
        }
        LLVMHeuristicOperation op = (LLVMHeuristicOperation)expr;
        if (op.getOperation() != ArithmeticOperationType.ADD) {
            return this;
        }
        LLVMHeuristicTerm opLhs = op.getLhs();
        LLVMHeuristicTerm opRhs = op.getRhs();
        for (int i = 0; i < allocs.size(); i++) {
            aborter.checkAbortion();
            LLVMAllocation alloc = allocs.get(i);
            if (alloc.x.equals(opLhs)) {
                return
                    this.checkArrayIndexForFurtherAssociation(
                        unassociatedRef,
                        index,
                        limit,
                        alloc,
                        i,
                        opRhs,
                        unassociatedPointerRefs,
                        newRels,
                        aborter
                    );
            } else if (alloc.x.equals(opRhs)) {
                return
                    this.checkArrayIndexForFurtherAssociation(
                        unassociatedRef,
                        index,
                        limit,
                        alloc,
                        i,
                        opLhs,
                        unassociatedPointerRefs,
                        newRels,
                        aborter
                    );
            }
        }
        return this;
    }

    /**
     * Attention: this method might yield tautological relations which must be cleaned thereafter!
     * @param rel An equation equivalent to y = rhs.
     * @param y The left-hand side of the equation.
     * @param rhs The right-hand side of the equation.
     * @param replacements The replacements conducted.
     * @param shrinking The shrunk intervals.
     * @return If rhs is of the form expr + x for a reference x and expression expr and we have a relation z = c1 + x
     *         for some constant c1 and reference z such that we know z >= y + c2 for some biggest constant c2, then
     *         c1 - c2 is applied as a bound to expr in the returned state. Otherwise, the returned state is just the
     *         current state.
     */
    private LLVMHeuristicState checkLimitRelation(
        LLVMHeuristicRelation rel,
        LLVMHeuristicVarRef y,
        LLVMHeuristicTerm rhs,
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements,
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> shrinking,
        Abortion aborter
    ) {
        if (!(rhs instanceof LLVMHeuristicOperation)) {
            // equation is not of the desired format
            return this;
        }
        LLVMHeuristicOperation op = (LLVMHeuristicOperation)rhs;
        switch (op.getOperation()) {
            case ADD:
                LLVMHeuristicTerm opLhs = op.getLhs();
                LLVMHeuristicTerm opRhs = op.getRhs();
                if (opLhs instanceof LLVMHeuristicVarRef) {
                    LLVMHeuristicState nextState =
                        this.checkLimitRelation(
                            (LLVMHeuristicVarRef)opLhs,
                            y,
                            opRhs,
                            replacements,
                            shrinking,
                            aborter
                        );
                    if (!this.equals(nextState)) {
                        return
                            nextState.checkLimitRelation(
                                rel.applySubstitution(replacements),
                                replacements,
                                shrinking,
                                aborter
                            );
                    }
                }
                if (opRhs instanceof LLVMHeuristicVarRef) {
                    LLVMHeuristicState nextState =
                        this.checkLimitRelation(
                            (LLVMHeuristicVarRef)opRhs,
                            y,
                            opLhs,
                            replacements,
                            shrinking,
                            aborter
                        );
                    if (!this.equals(nextState)) {
                        return
                            nextState.checkLimitRelation(
                                rel.applySubstitution(replacements),
                                replacements,
                                shrinking,
                                aborter
                            );
                    }
                }
                //$FALL-THROUGH$
            default:
                // equation is not of the desired format or we did not find out anything
                return this;
        }
    }

    /**
     * Attention: this method might yield tautological relations which must be cleaned thereafter!
     * @param rel An equation.
     * @param replacements The replacements conducted.
     * @param shrinking The shrunk non-constant intervals.
     * @return If the equation is of the form y = expr + x for two references x and y and some expression expr and we
     *         have a relation z = c1 + x for some constant c1 and reference z such that we know z >= y + c2 for some
     *         biggest constant c2, then c1 - c2 is applied as a bound to expr in the returned state. Otherwise, the
     *         returned state is just the current state.
     */
    private LLVMHeuristicState checkLimitRelation(
        LLVMHeuristicRelation rel,
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements,
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> shrinking,
        Abortion aborter
    ) {
        aborter.checkAbortion();
        LLVMHeuristicTerm lhs = rel.getLhs();
        LLVMHeuristicTerm rhs = rel.getRhs();
        if (lhs instanceof LLVMHeuristicVarRef) {
            return this.checkLimitRelation(rel, (LLVMHeuristicVarRef)lhs, rhs, replacements, shrinking, aborter);
        } else if (rhs instanceof LLVMHeuristicVarRef) {
            return this.checkLimitRelation(rel, (LLVMHeuristicVarRef)rhs, lhs, replacements, shrinking, aborter);
        } else {
            // equation is not of the desired format
            return this;
        }
    }

    /**
     * Attention: this method might yield tautological relations which must be cleaned thereafter!
     * @param x Some reference.
     * @param y Another reference.
     * @param expr Some expression.
     * @param replacements Replacements conducted during value adjustment.
     * @param shrinking Shrinking of intervals occurred during adjustment of values.
     * @return If expr is of the form a * r + b for a reference r and constants a and b such that b is positive and we
     *         have a relation z = c1 + x for some constant c1 and reference z such that we know z >= y + c2 for some
     *         biggest constant c2, then (c1 - c2 - b) / a is applied as a bound to r in the returned state. Otherwise,
     *         the returned state is just the current state.
     */
    private LLVMHeuristicState checkLimitRelation(
        LLVMHeuristicVarRef x,
        LLVMHeuristicVarRef y,
        LLVMHeuristicTerm expr,
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements,
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> shrinking,
        Abortion aborter
    ) {
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> linExpr = expr.toLinear();
        if (!(linExpr.x instanceof LLVMHeuristicVarRef) || linExpr.z.compareTo(BigInteger.ZERO) <= 0) {
            // expression is not of the desired format
            return this;
        }
        LLVMHeuristicState res = this;
        for (LLVMHeuristicRelation rel : this.getRelations()) {
            aborter.checkAbortion();
            if (!rel.isEquation()) {
                continue;
            }
            LLVMHeuristicTerm lhs = rel.getLhs();
            LLVMHeuristicTerm rhs = rel.getRhs();
            if (lhs instanceof LLVMHeuristicVarRef) {
                res =
                    res.checkLimitRelation(
                        x,
                        y,
                        linExpr,
                        (LLVMHeuristicVarRef)lhs,
                        rhs,
                        replacements,
                        shrinking
                    );
            } else if (rhs instanceof LLVMHeuristicVarRef) {
                res =
                    res.checkLimitRelation(
                        x,
                        y,
                        linExpr,
                        (LLVMHeuristicVarRef)rhs,
                        lhs,
                        replacements,
                        shrinking
                    );
            }
        }
        return res;
    }

    /**
     * Attention: this method might yield tautological relations which must be cleaned thereafter!
     * @param x Some reference.
     * @param y Another reference.
     * @param linExpr A reference with positive multiplicative factor and arbitrary additive constant.
     * @param z Yet another reference.
     * @param rhs Some expression such that z = rhs holds.
     * @param replacements Replacements conducted during value adjustment.
     * @param shrinking Shrinking of intervals occurred during adjustment of values.
     * @return If rhs is of the form c1 + x for a constant c1 such that we know z >= y + c2 for some biggest constant
     *         c2, then (c1 - c2 - linExpr.y) / linExpr.z is applied as a bound to linExpr.x in the returned state.
     *         Otherwise, the returned state is just the current state.
     */
    private LLVMHeuristicState checkLimitRelation(
        LLVMHeuristicVarRef x,
        LLVMHeuristicVarRef y,
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> linExpr,
        LLVMHeuristicVarRef z,
        LLVMHeuristicTerm rhs,
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements,
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> shrinking
    ) {
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> linRhs = rhs.toLinear();
        if (!x.equals(linRhs.x) || linRhs.z.compareTo(BigInteger.ONE) != 0) {
            return this;
        }
        BigInteger c2 = this.findBiggestConstantBetween(y, z);
        if (c2 == null) {
            return this;
        }
        BigInteger bound = linRhs.y.subtract(c2).subtract(linExpr.y).divide(linExpr.z);
        LLVMHeuristicVariable r = (LLVMHeuristicVarRef)linExpr.x;
        AbstractInt val = this.getValue(r).getThisAsAbstractInt();
        if (val.getUpper().compareTo(bound) <= 0) {
            return this;
        }
        if (Globals.useAssertions) {
            assert (val.getLower().compareTo(bound) <= 0) : "Inconsistent knowledge detected!";
        }
        if (val.getLower().compareTo(bound) == 0) {
            // r is a constant
            return
                this.unifyReferences(
                    r,
                    this.getRelationFactory().getTermFactory().constant(bound),
                    replacements,
                    shrinking
                );
        } else {
            if (shrinking.containsKey(r)) {
                shrinking.put(r, new Pair<BigInteger, BigInteger>(shrinking.get(r).x, bound));
            } else {
                shrinking.put(r, new Pair<BigInteger, BigInteger>(null, bound));
            }
            return this.setValue(r, val.setUpper(IntervalBound.create(bound)));
        }
    }

    /**
     * @param relRef A reference.
     * @param lhs Some expression.
     * @param rhsLinear A linearized expression.
     * @param unassociatedPointerRefs The yet unassociated references.
     * @param allocs The allocations.
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @return The state emerging from this state by adding further associations based on the knowledge that relRef has
     *         increased its value and lhs <= rhsLinear.y + rhsLinear.z * rhsLinear.y holds.
     */
    private LLVMHeuristicState checkRelForFurtherAssociations(
        LLVMHeuristicVariable relRef,
        LLVMHeuristicTerm lhs,
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear,
        Map<LLVMHeuristicVariable, TreeSet<LLVMPointerType>> unassociatedPointerRefs,
        ImmutableList<LLVMAllocation> allocs,
        Set<LLVMRelation> newRels,
        Abortion aborter
    ) {
        if (
            !(
                lhs instanceof LLVMHeuristicOperation
                && rhsLinear.x instanceof LLVMHeuristicVariable
                && rhsLinear.z.compareTo(BigInteger.ONE) == 0
            )
        ) {
            return this;
        }
        LLVMHeuristicOperation lhsOp = (LLVMHeuristicOperation)lhs;
        if (lhsOp.getOperation() != ArithmeticOperationType.ADD || !lhsOp.isSimple()) {
            return this;
        }
        LLVMHeuristicVariable smaller = null;
        if (lhsOp.getLhs().equals(relRef)) {
            smaller = (LLVMHeuristicVariable)lhsOp.getRhs();
        } else if (lhsOp.getRhs().equals(relRef)) {
            smaller = (LLVMHeuristicVariable)lhsOp.getLhs();
        }
        if (smaller == null) {
            return this;
        }
        ImmutableMap<LLVMHeuristicVariable, Integer> assocs = this.getAssociations();
        if (assocs.get(smaller) == null) {
            Integer association = assocs.get(rhsLinear.x);
            if (association == null) {
                return this;
            }
            LLVMHeuristicState res = this;
            // we can still check whether smaller itself can be associated
            for (Map.Entry<LLVMHeuristicVariable, TreeSet<LLVMPointerType>> entry : unassociatedPointerRefs.entrySet()) {
                if (!entry.getKey().equals(smaller)) {
                    continue;
                }
                LLVMAllocation allocation = allocs.get(association);
                res =
                    res.possiblyAddAssociation(
                        entry,
                        (LLVMHeuristicVariable)allocation.x,
                        (LLVMHeuristicVariable)allocation.y,
                        association,
                        newRels,
                        aborter
                    );
            }
            return res;
        } else {
            return
                this.findAndAddFurtherAssociations(
                    unassociatedPointerRefs,
                    smaller,
                    (LLVMHeuristicVariable)rhsLinear.x,
                    newRels,
                    aborter
                );
        }
    }

    /**
     * @param state The current state.
     * @param lhs The left-hand side of a relation.
     * @param rhs The right-hand side of a relation.
     * @param lhsLinear The left-hand side of a relation in linear form (passed as parameter to avoid re-computation).
     * @param rhsLinear The right-hand side of a relation in linear form (passed as parameter to avoid re-computation).
     * @param replacements The replacements conducted.
     * @param shrinking The shrinking map storing those intervals that got smaller.
     * @return The resulting state from checking whether some values must be shrunk according to the specified
     *         relation if this contains a remainder operation.
     */
    private LLVMHeuristicState checkRemainderOperation(
        LLVMHeuristicTerm lhs,
        LLVMHeuristicTerm rhs,
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear,
        Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear,
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements,
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> shrinking
    ) {
        BigInteger remRes = null;
        BigInteger remDiv = null;
        LLVMHeuristicOperation op = null;
        LLVMHeuristicVariable ref = null;
        if (lhs instanceof LLVMHeuristicConstRef) {
            remRes = ((LLVMHeuristicConstRef)lhs).getIntegerValue();
            if (rhsLinear.x instanceof LLVMHeuristicOperation) {
                op = (LLVMHeuristicOperation)rhsLinear.x;
                remRes = remRes.subtract(rhsLinear.y);
                if (remRes.remainder(rhsLinear.z).compareTo(BigInteger.ZERO) == 0) {
                    remRes = remRes.divide(rhsLinear.z);
                    LLVMHeuristicTerm opLhs = op.getLhs();
                    LLVMHeuristicTerm opRhs = op.getRhs();
                    if (opRhs instanceof LLVMHeuristicConstRef) {
                        remDiv = ((LLVMHeuristicConstRef)opRhs).getIntegerValue();
                    }
                    if (opLhs instanceof LLVMHeuristicVariable) {
                        ref = (LLVMHeuristicVariable)opLhs;
                    }
                }
            }
        } else if (rhs instanceof LLVMHeuristicConstRef) {
            remRes = ((LLVMHeuristicConstRef)rhs).getIntegerValue();
            if (lhsLinear.x instanceof LLVMHeuristicOperation) {
                op = (LLVMHeuristicOperation)lhsLinear.x;
                remRes = remRes.subtract(lhsLinear.y);
                if (remRes.remainder(lhsLinear.z).compareTo(BigInteger.ZERO) == 0) {
                    remRes = remRes.divide(lhsLinear.z);
                    LLVMHeuristicTerm opLhs = op.getLhs();
                    LLVMHeuristicTerm opRhs = op.getRhs();
                    if (opRhs instanceof LLVMHeuristicConstRef) {
                        remDiv = ((LLVMHeuristicConstRef)opRhs).getIntegerValue();
                    }
                    if (opLhs instanceof LLVMHeuristicVariable) {
                        ref = (LLVMHeuristicVariable)opLhs;
                    }
                }
            }
        }
        if (
            op != null
            && op.getOperation() == ArithmeticOperationType.TMOD
            && remRes != null
            && remDiv != null
            && ref != null
        ) {
            LLVMValue dividentValue = this.getValue(ref);
            AbstractInt dividentVal = dividentValue.getThisAsAbstractInt();
            boolean valChanged = false;
            IntervalBound lower = dividentVal.getLower();
            IntervalBound upper = dividentVal.getUpper();
            if (lower.isFinite()) {
                while (lower.getConstant().remainder(remDiv).compareTo(remRes) != 0) {
                    lower = lower.add(IntervalBound.ONE);
                    valChanged = true;
                }
            }
            if (upper.isFinite()) {
                while (upper.getConstant().remainder(remDiv).compareTo(remRes) != 0) {
                    upper = upper.add(IntervalBound.ONE.negate());
                    valChanged = true;
                }
            }
            if (valChanged) {
                LLVMValue nextVal = dividentVal.setLower(lower).setUpper(upper);
                if (upper.equals(lower)) {
                    return
                        this.unifyReferences(
                            ref,
                            this.getRelationFactory().getTermFactory().constant(lower.getConstant()),
                            replacements,
                            shrinking
                        );
                }
                LLVMHeuristicState res = this.setValue(ref, nextVal);
                if (shrinking.containsKey(ref)) {
                    Pair<BigInteger, BigInteger> old = shrinking.get(ref);
                    if (lower.isFinite() && (old.x == null || old.x.compareTo(lower.getConstant()) < 0)) {
                        old.x = lower.getConstant();
                    }
                    if (upper.isFinite() && (old.y == null || old.y.compareTo(upper.getConstant()) > 0)) {
                        old.y = upper.getConstant();
                    }
                } else {
                    shrinking.put(
                        ref,
                        new Pair<BigInteger, BigInteger>(
                            lower.isFinite() ? lower.getConstant() : null,
                            upper.isFinite() ? upper.getConstant() : null
                        )
                    );
                }
                return res;
            }
        }
        return this;
    }

    /**
     * @return A map from references to offsets known to be used as pointers (via a variable function
     *         within our call stack including the current function) and not being associated to an allocated memory
     *         area yet.
     */
    private Map<LLVMHeuristicVariable, TreeSet<LLVMPointerType>> computeUnassociatedAccesses() {
        final Map<LLVMHeuristicVariable, TreeSet<LLVMPointerType>> res =
            new LinkedHashMap<LLVMHeuristicVariable, TreeSet<LLVMPointerType>>();
        final LLVMPointerTypeOffsetComparator typeComp = new LLVMPointerTypeOffsetComparator();
        // add pointer refs from current function
        for (ImmutablePair<LLVMSymbolicVariable, LLVMType> varFuncValue : this.getProgramVariables().values()) {
            if (varFuncValue.y.isPointerType()) {
                if (!res.containsKey(varFuncValue.x)) {
                    res.put((LLVMHeuristicVariable)varFuncValue.x, new TreeSet<LLVMPointerType>(typeComp));
                }
                res.get(varFuncValue.x).add(varFuncValue.y.getThisAsPointerType());
            }
        }
        // add pointer refs from call stack
        for (LLVMReturnInformation retInfo : this.getCallStack()) {
            for (ImmutablePair<LLVMSymbolicVariable, LLVMType> varFuncValue : retInfo.getProgramVariables().values()) {
                if (varFuncValue.y.isPointerType()) {
                    if (!res.containsKey(varFuncValue.x)) {
                        res.put((LLVMHeuristicVariable)varFuncValue.x, new TreeSet<LLVMPointerType>(typeComp));
                    }
                    res.get(varFuncValue.x).add(varFuncValue.y.getThisAsPointerType());
                }
            }
        }
        // remove already associated refs
        final int pointerSize = this.getModule().getPointerSize();
        for (LLVMHeuristicVariable ref : this.getAssociations().keySet()) {
            if (!res.containsKey(ref)) {
                continue;
            }
            TreeSet<LLVMPointerType> set =
                new TreeSet<LLVMPointerType>(
                    res.get(
                        ref
                    ).tailSet(
                        new LLVMPointerType(
                            new LLVMIntType((this.getAssociationOffsets().get(ref).intValue() + 1) * 8),
                            pointerSize,
                            null
                        ),
                        false
                    )
                );
            if (set.isEmpty()) {
                res.remove(ref);
            } else {
                res.put(ref, set);
            }
        }
        return res;
    }

    /**
     * @param unassociatedAccesses Yet unassociated memory accesses.
     * @param smaller The smaller reference.
     * @param bigger The bigger reference.
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @return A state emerging from the specified state by adding further associations of yet unassociated memory
     *         accesses in case we can prove that these are between the two specified references or between one of them
     *         and the corresponding border reference of the associated allocated memory area.
     */
    private LLVMHeuristicState findAndAddFurtherAssociations(
        Map<LLVMHeuristicVariable, TreeSet<LLVMPointerType>> unassociatedAccesses,
        LLVMHeuristicVariable smaller,
        LLVMHeuristicVariable bigger,
        Set<LLVMRelation> newRels,
        Abortion aborter
    ) {
        LLVMHeuristicState res = this;
        ImmutableMap<LLVMHeuristicVariable, Integer> associations = res.getAssociations();
        Integer association = associations.get(smaller);
        if (association == null || !association.equals(associations.get(bigger))) {
            return res;
        }
        /*
         * Both smaller and bigger are associated to the same area:
         * => Refs between them must also be associated!
         * => Check unassociated pointer refs whether they belong to the same allocation!
         */
        LLVMAllocation allocation = res.getAllocations().get(association);
        LLVMHeuristicVariable left = (LLVMHeuristicVariable)allocation.x;
        LLVMHeuristicVariable right = (LLVMHeuristicVariable)allocation.y;
        res = res.addFurtherAssociations(unassociatedAccesses.entrySet().iterator(), left, right, association, newRels, aborter);
        /*
         * Moreover, size of allocated area may now known to be bigger than before.
         * Heuristic: Check relations about sizes of allocated areas for further associations!
         */
        Set<LLVMHeuristicVariable> upperRefs = new LinkedHashSet<LLVMHeuristicVariable>();
        Set<LLVMHeuristicVariable> lowerRefs = new LinkedHashSet<LLVMHeuristicVariable>();
        upperRefs.add(bigger);
        upperRefs.add(right);
        lowerRefs.add(smaller);
        lowerRefs.add(left);
        for (LLVMHeuristicRelation knownRel : res.getRelations()) {
            if (!knownRel.isDirectedInequality()) {
                continue;
            }
            LLVMHeuristicTerm lhs = knownRel.getLhs();
            LLVMHeuristicTerm rhs = knownRel.getRhs();
            if (!(lhs instanceof LLVMHeuristicOperation && rhs instanceof LLVMHeuristicOperation)) {
                continue;
            }
            LLVMHeuristicOperation lhsOp = (LLVMHeuristicOperation)lhs;
            LLVMHeuristicOperation rhsOp = (LLVMHeuristicOperation)rhs;
            if (
                !(
                    lhsOp.getOperation() == ArithmeticOperationType.ADD
                    && rhsOp.getOperation() == ArithmeticOperationType.ADD
                    && lhsOp.isSimple()
                    && rhsOp.isSimple()
                )
            ) {
                continue;
            }
            // found a standard relation between allocation sizes
            // now detect further allocations which we might check for associations
            Set<AllocationCandidate> allocCandidates =
                res.findFurtherAllocationCandidates(
                    lowerRefs,
                    upperRefs,
                    (LLVMHeuristicVariable)lhsOp.getLhs(),
                    (LLVMHeuristicVariable)lhsOp.getRhs(),
                    (LLVMHeuristicVariable)rhsOp.getLhs(),
                    (LLVMHeuristicVariable)rhsOp.getRhs()
                );
            for (AllocationCandidate furtherAlloc : allocCandidates) {
                res =
                    res.addFurtherAssociations(
                        unassociatedAccesses.entrySet().iterator(),
                        (LLVMHeuristicVariable)furtherAlloc.x.x,
                        (LLVMHeuristicVariable)furtherAlloc.x.y,
                        furtherAlloc.y,
                        newRels,
                        aborter
                    );
            }
        }
        return res;
    }

    /**
     * TODO add more ways to find constants, maybe use full reasoning?
     * @param x Some reference.
     * @param y Another reference.
     * @return The biggest constant c such that x + c <= y is valid in the current state. This method works
     *         heuristically and may not return the actually biggest constant, but just an approximation. It returns
     *         null if it cannot find such a constant.
     */
    private BigInteger findBiggestConstantBetween(LLVMHeuristicVariable x, LLVMHeuristicVariable y) {
        if (x.equals(y)) {
            return BigInteger.ZERO;
        }
        BigInteger res = null;
        // check relations
        for (LLVMHeuristicRelation rel : this.getRelations()) {
            if (rel.getHeuristicRelationType() == LLVMHeuristicRelationType.NE) {
                continue;
            }
            LLVMHeuristicTerm lhs = rel.getLhs();
            LLVMHeuristicTerm rhs = rel.getRhs();
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> lhsLinear = lhs.toLinear();
            Triple<LLVMHeuristicTerm, BigInteger, BigInteger> rhsLinear = rhs.toLinear();
            if (
                !(lhsLinear.x instanceof LLVMHeuristicVarRef)
                || !(rhsLinear.x instanceof LLVMHeuristicVarRef)
                || lhsLinear.z.compareTo(BigInteger.ONE) != 0
                || rhsLinear.z.compareTo(BigInteger.ONE) != 0
                || lhsLinear.y.compareTo(BigInteger.ZERO) < 0
                || rhsLinear.y.compareTo(BigInteger.ZERO) < 0
            ) {
                continue;
            }
            if (rel.isEquation()) {
                if (lhs.equals(y)) {
                    BigInteger next = this.findBiggestConstantBetween(x, (LLVMHeuristicVarRef)rhsLinear.x);
                    if (next != null) {
                        BigInteger added = next.add(rhsLinear.y);
                        if (res == null || res.compareTo(added) < 0) {
                            res = added;
                        }
                    }
                }
                if (rhs.equals(y)) {
                    BigInteger next = this.findBiggestConstantBetween(x, (LLVMHeuristicVarRef)lhsLinear.x);
                    if (next != null) {
                        BigInteger added = next.add(lhsLinear.y);
                        if (res == null || res.compareTo(added) < 0) {
                            res = added;
                        }
                    }
                }
                if (lhsLinear.x.equals(x) && rhs instanceof LLVMHeuristicVarRef) {
                    BigInteger next = this.findBiggestConstantBetween((LLVMHeuristicVarRef)rhs, y);
                    if (next != null) {
                        BigInteger added = next.add(lhsLinear.y);
                        if (res == null || res.compareTo(added) < 0) {
                            res = added;
                        }
                    }
                }
                if (rhsLinear.x.equals(x) && lhs instanceof LLVMHeuristicVarRef) {
                    BigInteger next = this.findBiggestConstantBetween((LLVMHeuristicVarRef)lhs, y);
                    if (next != null) {
                        BigInteger added = next.add(rhsLinear.y);
                        if (res == null || res.compareTo(added) < 0) {
                            res = added;
                        }
                    }
                }
            } else {
                if (rhs.equals(y)) {
                    BigInteger next = this.findBiggestConstantBetween(x, (LLVMHeuristicVarRef)lhsLinear.x);
                    if (next != null) {
                        BigInteger added = next.add(lhsLinear.y);
                        if (rel.isStrictInequality()) {
                            added = added.add(BigInteger.ONE);
                        }
                        if (res == null || res.compareTo(added) < 0) {
                            res = added;
                        }
                    }
                }
                if (lhsLinear.x.equals(x) && rhs instanceof LLVMHeuristicVarRef) {
                    BigInteger next = this.findBiggestConstantBetween((LLVMHeuristicVarRef)rhs, y);
                    if (next != null) {
                        BigInteger added = next.add(lhsLinear.y);
                        if (rel.isStrictInequality()) {
                            added = added.add(BigInteger.ONE);
                        }
                        if (res == null || res.compareTo(added) < 0) {
                            res = added;
                        }
                    }
                }
            }
        }
        // check associations
        ImmutableMap<LLVMHeuristicVariable, Integer> assocs = this.getAssociations();
        if (assocs.containsKey(x)) {
            LLVMHeuristicVariable border = (LLVMHeuristicVariable)this.getAllocations().get(assocs.get(x)).y;
            if (!x.equals(border)) {
                BigInteger next = this.findBiggestConstantBetween(border, y);
                if (next != null) {
                    BigInteger added = next.add(this.getAssociationOffsets().get(x));
                    if (res == null || res.compareTo(added) < 0) {
                        res = added;
                    }
                }
            }
        }
        if (assocs.containsKey(y)) {
            LLVMHeuristicVariable border = (LLVMHeuristicVariable)this.getAllocations().get(assocs.get(y)).x;
            if (!y.equals(border)) {
                BigInteger next = this.findBiggestConstantBetween(x, border);
                if (next != null && (res == null || res.compareTo(next) < 0)) {
                    res = next;
                }
            }
        }
        return res;
    }

    /**
     * @param lowerRefs References known to be strictly smaller than those in upperRefs, yet in the same allocation.
     * @param upperRefs References known to be strictly bigger than those in lowerRefs, yet in the same allocation.
     * @param lhsLeft The left reference on the left-hand side of a standard relation between allocation sizes.
     * @param lhsRight The right reference on the left-hand side of a standard relation between allocation sizes.
     * @param rhsLeft The left reference on the right-hand side of a standard relation between allocation sizes.
     * @param rhsRight The right reference on the right-hand side of a standard relation between allocation sizes.
     * @return A set of allocations and corresponding indices for which we have possibly learned a bigger size.
     */
    private Set<AllocationCandidate> findFurtherAllocationCandidates(
        Set<LLVMHeuristicVariable> lowerRefs,
        Set<LLVMHeuristicVariable> upperRefs,
        LLVMHeuristicVariable lhsLeft,
        LLVMHeuristicVariable lhsRight,
        LLVMHeuristicVariable rhsLeft,
        LLVMHeuristicVariable rhsRight
    ) {
        Set<AllocationCandidate> res = new LinkedHashSet<AllocationCandidate>();
        for (LLVMHeuristicVariable upper : upperRefs) {
            for (LLVMHeuristicVariable lower : lowerRefs) {
                if (lhsLeft.equals(upper)) {
                    if (rhsLeft.equals(lower)) {
                        Integer associationCandidate = this.getAssociations().get(lhsRight);
                        if (
                            associationCandidate != null
                            && associationCandidate.equals(this.getAssociations().get(rhsRight))
                        ) {
                            res.add(
                                new AllocationCandidate(
                                    this.getAllocations().get(associationCandidate),
                                    associationCandidate
                                )
                            );
                        }
                    } else if (rhsRight.equals(lower)) {
                        Integer associationCandidate = this.getAssociations().get(lhsRight);
                        if (
                            associationCandidate != null
                            && associationCandidate.equals(this.getAssociations().get(rhsLeft))
                        ) {
                            res.add(
                                new AllocationCandidate(
                                    this.getAllocations().get(associationCandidate),
                                    associationCandidate
                                )
                            );
                        }
                    }
                } else if (lhsRight.equals(upper)) {
                    if (rhsLeft.equals(lower)) {
                        Integer associationCandidate = this.getAssociations().get(lhsLeft);
                        if (
                            associationCandidate != null
                            && associationCandidate.equals(this.getAssociations().get(rhsRight))
                        ) {
                            res.add(
                                new AllocationCandidate(
                                    this.getAllocations().get(associationCandidate),
                                    associationCandidate
                                )
                            );
                        }
                    } else if (rhsRight.equals(lower)) {
                        Integer associationCandidate = this.getAssociations().get(lhsLeft);
                        if (
                            associationCandidate != null
                            && associationCandidate.equals(this.getAssociations().get(rhsLeft))
                        ) {
                            res.add(
                                new AllocationCandidate(
                                    this.getAllocations().get(associationCandidate),
                                    associationCandidate
                                )
                            );
                        }
                    }
                }
            }
        }
        return res;
    }

    /**
     * @param shrinking The map from references to their new lower/upper limits (except for replaced references).
     * @param replacements The replacements conducted.
     * @param ref Some reference.
     * @param sameOffset Offset from <code>ref</code> (with factor).
     * @param sameFactor Factor to <code>ref</code>.
     * @param otherOffset Offset at the other side of the equation.
     * @param otherFactor Factor at the other side of the equation.
     * @return The state emerging from this state by adjusting the limits of ref's value to be consistent with the
     *         multiplications performed by the specified factors.
     */
    private LLVMHeuristicState handleMultiplicationCase(
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> shrinking,
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements,
        LLVMHeuristicVariable ref,
        BigInteger sameOffset,
        BigInteger sameFactor,
        BigInteger otherOffset,
        BigInteger otherFactor
    ) {
        LLVMValue leftValue = this.getValue(ref);
        AbstractBoundedInt leftVal = leftValue.getThisAsAbstractBoundedInt();
        IntervalBound leftLower = leftVal.getLower();
        IntervalBound leftUpper = leftVal.getUpper();
        boolean changed = false;
        BigInteger leftLowConst = null;
        if (leftLower.isFinite()) {
            leftLowConst = leftLower.getConstant();
            while (
                leftLowConst.multiply(
                    sameFactor
                ).add(
                    sameOffset
                ).subtract(otherOffset).remainder(otherFactor).compareTo(BigInteger.ZERO) != 0
            ) {
                leftLowConst = leftLowConst.add(BigInteger.ONE);
            }
            if (leftLowConst.compareTo(leftLower.getConstant()) != 0) {
                leftLower = IntervalBound.create(leftLowConst);
                changed = true;
            }
        }
        BigInteger leftUpConst = null;
        if (leftUpper.isFinite()) {
            leftUpConst = leftUpper.getConstant();
            while (
                leftUpConst.multiply(
                    sameFactor
                ).add(
                    sameOffset
                ).subtract(otherOffset).remainder(otherFactor).compareTo(BigInteger.ZERO) != 0
            ) {
                leftUpConst = leftUpConst.subtract(BigInteger.ONE);
            }
            if (leftUpConst.compareTo(leftUpper.getConstant()) != 0) {
                leftUpper = IntervalBound.create(leftUpConst);
                changed = true;
            }
        }
        if (changed) {
            if (shrinking.containsKey(ref)) {
                Pair<BigInteger, BigInteger> old = shrinking.get(ref);
                if (leftLowConst != null) {
                    if (old.x == null || old.x.compareTo(leftLowConst) < 0) {
                        old.x = leftLowConst;
                    }
                }
                if (leftUpConst != null) {
                    if (old.y == null || old.y.compareTo(leftUpConst) > 0) {
                        old.y = leftUpConst;
                    }
                }
                if (old.x != null && old.y != null && old.x.compareTo(old.y) == 0) {
                    return
                        this.unifyReferences(
                            ref,
                            this.getRelationFactory().getTermFactory().constant(old.x),
                            replacements,
                            shrinking
                        );
                }
            } else if (
                leftLowConst != null && leftUpConst != null && leftLowConst.compareTo(leftUpConst) == 0
            ) {
                return
                    this.unifyReferences(
                        ref,
                        this.getRelationFactory().getTermFactory().constant(leftLowConst),
                        replacements,
                        shrinking
                    );
            } else {
                shrinking.put(ref, new Pair<BigInteger, BigInteger>(leftLowConst, leftUpConst));
            }
            AbstractBoundedInt afterLower = leftVal.setLower(leftLower);
        	if(afterLower == null) {
        		throw new InconsistentStateException(null, null);
        	}
        	AbstractBoundedInt afterUpper = afterLower.setUpper(leftUpper);
        	if(afterUpper == null) {
        		throw new InconsistentStateException(null, null);
        	}
            return this.setValue(ref, afterUpper);
        }
        return this;
    }

    /**
     * @param shrinking The map from references to their new lower/upper limits (except for replaced references).
     * @param replacements The replacements conducted.
     * @param ref Some reference.
     * @param sameOffset Offset from <code>ref</code> (with factor).
     * @param sameFactor Factor to <code>ref</code>.
     * @param otherOffset Offset at the other side of the equation.
     * @param otherFactor Factor at the other side of the equation.
     * @return The state emerging from this state by adjusting the limits of ref's value to be consistent with the
     *         multiplications performed by the specified factors.
     */
    private LLVMHeuristicState handleMultiplicationCase(
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> shrinking,
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements,
        LLVMHeuristicVariable firstRef,
        BigInteger firstOffset,
        BigInteger firstFactor,
        LLVMHeuristicVariable secondRef,
        BigInteger secondOffset,
        BigInteger secondFactor
    ) {
        LLVMHeuristicState res = this;
        LLVMValue firstValue = this.getValue(firstRef);
        AbstractBoundedInt firstVal = firstValue.getThisAsAbstractBoundedInt();
        IntervalBound firstLower = firstVal.getLower();
        IntervalBound firstUpper = firstVal.getUpper();
        LLVMValue secondValue = this.getValue(secondRef);
        AbstractBoundedInt secondVal = secondValue.getThisAsAbstractBoundedInt();
        IntervalBound secondLower = secondVal.getLower();
        IntervalBound secondUpper = secondVal.getUpper();
        boolean firstLowChanged = false;
        boolean firstUpChanged = false;
        boolean secondLowChanged = false;
        boolean secondUpChanged = false;
        BigInteger firstLowConst = null;
        BigInteger firstUpConst = null;
        BigInteger secondLowConst = null;
        BigInteger secondUpConst = null;
        // We have firstFactor * firstVal + firstOffset = secondFactor * secondVal + secondOffset
        //   <=>   firstVal = (secondFactor * secondVal + secondOffset - firstOffset) / firstFactor
        //   and   secondVal = (firstFactor * firstVal + firstOffset - secondOffset) / secondFactor
        assert (firstFactor.signum() != 0 && secondFactor.signum() != 0);
        // If sgn(firstFactor) == sgn(secondFactor), then
        //         firstLower = (secondFactor * secondLower + secondOffset - firstOffset) / firstFactor
        //   and   firstUpper = (secondFactor * secondUpper + secondOffset - firstOffset) / firstFactor
        //   and   secondLower = (firstFactor * firstLower + firstOffset - secondOffset) / secondFactor
        //   and   secondUpper = (firstFactor * firstUpper + firstOffset - secondOffset) / secondFactor
        // where we have to round correctly (round up positive lower bounds, round down negative upper bounds)
        if (firstFactor.signum() == secondFactor.signum()) {
            if (firstLower.isFinite()) {
                firstLowConst = firstLower.getConstant();
                BigInteger dividend = firstLowConst.multiply(firstFactor).add(firstOffset).subtract(secondOffset);
                BigInteger[] divAndRem = dividend.divideAndRemainder(secondFactor);
                secondLowConst = divAndRem[0];
                if (divAndRem[1].compareTo(BigInteger.ZERO) != 0 && dividend.signum() == secondFactor.signum()) {
                    secondLowConst = secondLowConst.add(BigInteger.ONE);
                }
                dividend = secondLowConst.multiply(secondFactor).add(secondOffset).subtract(firstOffset);
                divAndRem = dividend.divideAndRemainder(firstFactor);
                firstLowConst = divAndRem[0];
                if (divAndRem[1].compareTo(BigInteger.ZERO) != 0 && dividend.signum() == firstFactor.signum()) {
                    firstLowConst = firstLowConst.add(BigInteger.ONE);
                }
            } else if (secondLower.isFinite()) {
                secondLowConst = secondLower.getConstant();
                BigInteger dividend = secondLowConst.multiply(secondFactor).add(secondOffset).subtract(firstOffset);
                BigInteger[] divAndRem = dividend.divideAndRemainder(firstFactor);
                firstLowConst = divAndRem[0];
                if (divAndRem[1].compareTo(BigInteger.ZERO) != 0 && dividend.signum() == firstFactor.signum()) {
                    firstLowConst = firstLowConst.add(BigInteger.ONE);
                }
            }
            if (firstUpper.isFinite()) {
                firstUpConst = firstUpper.getConstant();
                BigInteger dividend = firstUpConst.multiply(firstFactor).add(firstOffset).subtract(secondOffset);
                BigInteger[] divAndRem = dividend.divideAndRemainder(secondFactor);
                secondUpConst = divAndRem[0];
                if (divAndRem[1].compareTo(BigInteger.ZERO) != 0 && dividend.signum() != secondFactor.signum()) {
                    secondUpConst = secondUpConst.subtract(BigInteger.ONE);
                }
                dividend = secondUpConst.multiply(secondFactor).add(secondOffset).subtract(firstOffset);
                divAndRem = dividend.divideAndRemainder(firstFactor);
                firstUpConst = divAndRem[0];
                if (divAndRem[1].compareTo(BigInteger.ZERO) != 0 && dividend.signum() != firstFactor.signum()) {
                    firstUpConst = firstUpConst.subtract(BigInteger.ONE);
                }
            } else if (secondUpper.isFinite()) {
                secondUpConst = secondUpper.getConstant();
                BigInteger dividend = secondUpConst.multiply(secondFactor).add(secondOffset).subtract(firstOffset);
                BigInteger[] divAndRem = dividend.divideAndRemainder(firstFactor);
                firstUpConst = divAndRem[0];
                if (divAndRem[1].compareTo(BigInteger.ZERO) != 0 && dividend.signum() != firstFactor.signum()) {
                    firstUpConst = firstUpConst.subtract(BigInteger.ONE);
                }
            }
        } else {
            // If sgn(firstFactor) != sgn(secondFactor), then
            //         firstLower = (secondFactor * secondUpper + secondOffset - firstOffset) / firstFactor
            //   and   firstUpper = (secondFactor * secondLower + secondOffset - firstOffset) / firstFactor
            //   and   secondLower = (firstFactor * firstUpper + firstOffset - secondOffset) / secondFactor
            //   and   secondUpper = (firstFactor * firstLower + firstOffset - secondOffset) / secondFactor
            // where we have to round correctly (round up positive lower bounds, round down negative upper bounds)
            if (firstLower.isFinite()) {
                firstLowConst = firstLower.getConstant();
                BigInteger dividend = firstLowConst.multiply(firstFactor).add(firstOffset).subtract(secondOffset);
                BigInteger[] divAndRem = dividend.divideAndRemainder(secondFactor);
                secondUpConst = divAndRem[0];
                if (divAndRem[1].compareTo(BigInteger.ZERO) != 0 && dividend.signum() != secondFactor.signum()) {
                    secondUpConst = secondUpConst.subtract(BigInteger.ONE);
                }
                dividend = secondUpConst.multiply(secondFactor).add(secondOffset).subtract(firstOffset);
                divAndRem = dividend.divideAndRemainder(firstFactor);
                firstLowConst = divAndRem[0];
                if (divAndRem[1].compareTo(BigInteger.ZERO) != 0 && dividend.signum() == firstFactor.signum()) {
                    firstLowConst = firstLowConst.add(BigInteger.ONE);
                }
            } else if (secondUpper.isFinite()) {
                secondUpConst = secondUpper.getConstant();
                BigInteger dividend = secondUpConst.multiply(secondFactor).add(secondOffset).subtract(firstOffset);
                BigInteger[] divAndRem = dividend.divideAndRemainder(firstFactor);
                firstLowConst = divAndRem[0];
                if (divAndRem[1].compareTo(BigInteger.ZERO) != 0 && dividend.signum() == firstFactor.signum()) {
                    firstLowConst = firstLowConst.add(BigInteger.ONE);
                }
            }
            if (firstUpper.isFinite()) {
                firstUpConst = firstUpper.getConstant();
                BigInteger dividend = firstUpConst.multiply(firstFactor).add(firstOffset).subtract(secondOffset);
                BigInteger[] divAndRem = dividend.divideAndRemainder(secondFactor);
                secondLowConst = divAndRem[0];
                if (divAndRem[1].compareTo(BigInteger.ZERO) != 0 && dividend.signum() == secondFactor.signum()) {
                    secondLowConst = secondLowConst.add(BigInteger.ONE);
                }
                dividend = secondLowConst.multiply(secondFactor).add(secondOffset).subtract(firstOffset);
                divAndRem = dividend.divideAndRemainder(firstFactor);
                firstUpConst = divAndRem[0];
                if (divAndRem[1].compareTo(BigInteger.ZERO) != 0 && dividend.signum() != firstFactor.signum()) {
                    firstUpConst = firstUpConst.subtract(BigInteger.ONE);
                }
            } else if (secondLower.isFinite()) {
                secondLowConst = secondLower.getConstant();
                BigInteger dividend = secondLowConst.multiply(secondFactor).add(secondOffset).subtract(firstOffset);
                BigInteger[] divAndRem = dividend.divideAndRemainder(firstFactor);
                firstUpConst = divAndRem[0];
                if (divAndRem[1].compareTo(BigInteger.ZERO) != 0 && dividend.signum() != firstFactor.signum()) {
                    firstUpConst = firstUpConst.subtract(BigInteger.ONE);
                }
            }
        }
        // Check if something has changed.
        if (!firstLower.isFinite() && firstLowConst != null ||
                firstLower.isFinite() && firstLowConst.compareTo(firstLower.getConstant()) > 0) {
            firstLower = IntervalBound.create(firstLowConst);
            firstLowChanged = true;
        }
        if (!firstUpper.isFinite() && firstUpConst != null ||
                firstUpper.isFinite() && firstUpConst.compareTo(firstUpper.getConstant()) < 0) {
            firstUpper = IntervalBound.create(firstUpConst);
            firstUpChanged = true;
        }
        if (!secondLower.isFinite() && secondLowConst != null ||
                secondLower.isFinite() && secondLowConst.compareTo(secondLower.getConstant()) > 0) {
            secondLower = IntervalBound.create(secondLowConst);
            secondLowChanged = true;
        }
        if (!secondUpper.isFinite() && secondUpConst != null ||
                secondUpper.isFinite() && secondUpConst.compareTo(secondUpper.getConstant()) < 0) {
            secondUpper = IntervalBound.create(secondUpConst);
            secondUpChanged = true;
        }
        final LLVMHeuristicTermFactory termFactory = this.getRelationFactory().getTermFactory();
        // Handle first reference.
        if (firstLowChanged || firstUpChanged) {
            if (shrinking.containsKey(firstRef)) {
                Pair<BigInteger, BigInteger> old = shrinking.get(firstRef);
                if (firstLowChanged) {
                    if (old.x == null || old.x.compareTo(firstLowConst) < 0) {
                        old.x = firstLowConst;
                    }
                }
                if (firstUpChanged) {
                    if (old.y == null || old.y.compareTo(firstUpConst) > 0) {
                        old.y = firstUpConst;
                    }
                }
                if (old.x != null && old.y != null && old.x.compareTo(old.y) == 0) {
                    res = this.unifyReferences(firstRef, termFactory.constant(old.x), replacements, shrinking);
                }
            } else if (
                firstLowChanged && firstUpChanged && firstLowConst.compareTo(firstUpConst) == 0
            ) {
                res = this.unifyReferences(firstRef, termFactory.constant(firstLowConst), replacements, shrinking);
            } else {
                shrinking.put(firstRef, new Pair<BigInteger, BigInteger>(firstLowConst, firstUpConst));
            }
            AbstractBoundedInt afterLower = firstVal.setLower(firstLower);
            if(afterLower == null) {
        		throw new InconsistentStateException(null, null);
        	}
            AbstractBoundedInt afterUpper = afterLower.setUpper(firstUpper);
            if(afterUpper == null) {
        		throw new InconsistentStateException(null, null);
        	}
            res = this.setValue(firstRef, afterUpper);
        }
        // Handle second reference.
        if (secondLowChanged || secondUpChanged) {
            if (shrinking.containsKey(secondRef)) {
                Pair<BigInteger, BigInteger> old = shrinking.get(secondRef);
                if (secondLowChanged) {
                    if (old.x == null || old.x.compareTo(secondLowConst) < 0) {
                        old.x = secondLowConst;
                    }
                }
                if (secondUpChanged) {
                    if (old.y == null || old.y.compareTo(secondUpConst) > 0) {
                        old.y = secondUpConst;
                    }
                }
                if (old.x != null && old.y != null && old.x.compareTo(old.y) == 0) {
                    res = this.unifyReferences(secondRef, termFactory.constant(old.x), replacements, shrinking);
                }
            } else if (
                secondLowChanged && secondUpChanged && secondLowConst.compareTo(secondUpConst) == 0
            ) {
                res = this.unifyReferences(secondRef, termFactory.constant(secondLowConst), replacements, shrinking);
            } else {
                shrinking.put(secondRef, new Pair<BigInteger, BigInteger>(secondLowConst, secondUpConst));
            }
            res = this.setValue(secondRef, secondVal.setLower(secondLower).setUpper(secondUpper));
        }
        return res;
    }

    /**
     * @param shrinking The map from references to their new lower/upper limits.
     * @param ref Some reference.
     * @param unequal A constant being unequal to the reference.
     * @return The state emerging from this state by adding the knowledge that the specified reference is unequal to
     *         the specified constant value. Moreover, the shrinking map is updated accordingly.
     */
    private LLVMReplacementResult handleSimplePureInequality(
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> shrinking,
        LLVMHeuristicVariable ref,
        BigInteger unequal
    ) {
        LLVMHeuristicState res = this;
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements =
            new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>();
        LLVMValue value = res.getValue(ref);
        AbstractBoundedInt val = value.getThisAsAbstractBoundedInt();
        final LLVMHeuristicTermFactory termFactory = this.getRelationFactory().getTermFactory();
        if (unequal.compareTo(BigInteger.ZERO) == 0) {
            if (val.containsInt(AbstractBoundedInt.getZero())) {
                res = res.setValue(ref, val.removeZeroFromInteger());
                if (val.isNonNegative()) {
                    // ref >= 1
                    if (shrinking.containsKey(ref)) {
                        Pair<BigInteger, BigInteger> old = shrinking.get(ref);
                        if (old.x == null || old.x.compareTo(BigInteger.ONE) < 0) {
                            old.x = BigInteger.ONE;
                            if (old.y != null && old.y.compareTo(old.x) == 0) {
                                replacements.put(ref, termFactory.one());
                                res = res.replaceSymbolicVariable(ref, termFactory.one());
                                shrinking.remove(ref);
                            }
                        }
                    } else {
                        shrinking.put(ref, new Pair<BigInteger, BigInteger>(BigInteger.ONE, null));
                    }
                } else if (val.isNonPositive()) {
                    // ref <= -1
                    if (shrinking.containsKey(ref)) {
                        Pair<BigInteger, BigInteger> old = shrinking.get(ref);
                        if (old.y == null || old.y.compareTo(IntegerUtils.NEGONE) > 0) {
                            old.y = IntegerUtils.NEGONE;
                            if (old.x != null && old.x.compareTo(old.y) == 0) {
                                replacements.put(ref, termFactory.negone());
                                res =
                                    res.replaceSymbolicVariable(ref, termFactory.negone());
                                shrinking.remove(ref);
                            }
                        }
                    } else {
                        shrinking.put(ref, new Pair<BigInteger, BigInteger>(null, IntegerUtils.NEGONE));
                    }
                }
            }
        } else {
            IntervalBound lower = val.getLower();
            IntervalBound upper = val.getUpper();
            boolean changed = false;
            if (lower.isFinite() && lower.getConstant().compareTo(unequal) == 0) {
                lower = lower.add(IntervalBound.ONE);
                changed = true;
            }
            if (upper.isFinite() && upper.getConstant().compareTo(unequal) == 0) {
                upper = upper.add(IntervalBound.NEGONE);
                changed = true;
            }
            if (changed) {
                if (lower.equals(upper)) {
                    LLVMHeuristicConstRef constant = termFactory.constant(lower.getConstant());
                    res = res.replaceSymbolicVariable(ref, constant);
                    replacements.put(ref, constant);
                    shrinking.remove(ref);
                } else {
                	AbstractBoundedInt afterLower = val.setLower(lower);
                	if(afterLower == null) {
                		throw new InconsistentStateException(null, null);
                	}
                	AbstractBoundedInt afterUpper = afterLower.setUpper(upper);
                	if(afterUpper == null) {
                		throw new InconsistentStateException(null, null);
                	}
                    res = res.setValue(ref, afterUpper);
                    if (shrinking.containsKey(ref)) {
                        Pair<BigInteger, BigInteger> old = shrinking.get(ref);
                        if (lower.isFinite() && (old.x == null || old.x.compareTo(lower.getConstant()) < 0)) {
                            old.x = lower.getConstant();
                        }
                        if (upper.isFinite() && (old.y == null || old.y.compareTo(upper.getConstant()) > 0)) {
                            old.y = upper.getConstant();
                        }
                        if (old.x != null && old.y != null && old.x.compareTo(old.y) == 0) {
                            LLVMHeuristicConstRef constant = termFactory.constant(old.x);
                            res = res.replaceSymbolicVariable(ref, constant);
                            replacements.put(ref, constant);
                            shrinking.remove(ref);
                        }
                    } else {
                        shrinking.put(
                            ref,
                            new Pair<BigInteger, BigInteger>(
                                lower.isFinite() ? lower.getConstant() : null,
                                upper.isFinite() ? upper.getConstant() : null
                            )
                        );
                    }
                }
            }
        }
        return new LLVMReplacementResult(res, replacements);
    }

    /**
     * @param access A map entry for an unassociated memory access.
     * @param left The left border of the allocation.
     * @param right The right border of the allocation.
     * @param association The index of the specified allocation within the allocation list.
     * @param newRels In not <code>null</code> new relations will be added to this set
     * @return A state emerging from the specified state by adding a further association to the yet unassociated memory
     *         access in case we can prove that it is between the allocation border variables.
     */
    private LLVMHeuristicState possiblyAddAssociation(
        Map.Entry<LLVMHeuristicVariable, TreeSet<LLVMPointerType>> access,
        LLVMHeuristicVariable left,
        LLVMHeuristicVariable right,
        Integer association,
        Set<LLVMRelation> newRels,
        Abortion aborter
    ) {
        final LLVMHeuristicTermFactory termFactory = this.getRelationFactory().getTermFactory();
        LLVMHeuristicVariable ref = access.getKey();
        TreeSet<LLVMPointerType> remainingSet = new TreeSet<LLVMPointerType>(new LLVMPointerTypeOffsetComparator());
        LLVMHeuristicState res = this;
        for (LLVMPointerType type : access.getValue().descendingSet()) {
            Pair<Boolean, ? extends LLVMAbstractState> check =
                res.checkRelation(
                    termFactory.upperAddress(ref, type.toOffset()),
                    IntegerRelationType.LE,
                    right,
                    aborter
                );
            res = (LLVMHeuristicState)check.y;
            if (check.x) {
                check = res.checkRelation(left, IntegerRelationType.LE, ref, aborter);
                res = (LLVMHeuristicState)check.y;
                if (check.x) {
                    access.setValue(remainingSet);
                    return res.associateAccess(ref, type, association, newRels, aborter);
                }
            }
            remainingSet.add(type);
        }
        return res;
    }

    /**
     * @param replacements The replacements. This map might be modified by this method to add further replacements.
     * @return A state where the specified reference replacements have been performed.
     */
    private LLVMHeuristicState replaceReferences(Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements) {
        // Variables:
        Map<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> newVars =
            new LinkedHashMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>>(this.getProgramVariables());
        for (Map.Entry<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> e : newVars.entrySet()) {
            ImmutablePair<LLVMSymbolicVariable, LLVMType> val = e.getValue();
            if (replacements.containsKey(val.x)) {
                e.setValue(new ImmutablePair<LLVMSymbolicVariable, LLVMType>(replacements.get(val.x), val.y));
            }
        }
        // Dereferencings:
        Map<LLVMMemoryRange, LLVMMemoryInvariant> newMemory =
            new LinkedHashMap<LLVMMemoryRange, LLVMMemoryInvariant>(this.getMemory());
        for (Map.Entry<LLVMMemoryRange, LLVMMemoryInvariant> entry : this.getMemory().entrySet()) {
            LLVMMemoryRange range = entry.getKey();
            LLVMSimpleTerm new_from_ref = range.getFromRef();
            LLVMSimpleTerm new_to_ref = range.getToRef();
            if (replacements.containsKey(new_from_ref)) {
                new_from_ref = replacements.get(new_from_ref);
            }
            if (replacements.containsKey(new_to_ref)) {
                new_to_ref = replacements.get(new_to_ref);
            }
            LLVMSimpleTerm new_length = null;
            if (range instanceof LLVMMemoryRecursiveRange) {
                if (replacements.containsKey(((LLVMMemoryRecursiveRange)range).getLength())) {
                    new_length = replacements.get(((LLVMMemoryRecursiveRange)range).getLength());
                } else {
                    new_length = ((LLVMMemoryRecursiveRange)range).getLength();
                }
            }
            newMemory.remove(range);
            LLVMMemoryRange newPair;
            if (range instanceof LLVMMemoryRecursiveRange) {
                newPair = new LLVMMemoryRecursiveRange(new_from_ref, new_to_ref, range.getType(), new_length);
            } else {
                newPair = new LLVMMemoryRange(new_from_ref,new_to_ref, range.getType(), range.getUnsigned());
            }
            LLVMMemoryInvariant value = entry.getValue().replaceReferences(replacements);
            if (Globals.useAssertions) {
                LLVMMemoryInvariant otherVal = this.getMemory().get(newPair);
                if (otherVal instanceof LLVMSimpleMemoryInvariant) {
                    if (value instanceof LLVMSimpleMemoryInvariant) {
                        LLVMSimpleTerm other_to = ((LLVMSimpleMemoryInvariant)otherVal).getPointedToValue();
                        LLVMSimpleTerm this_to = ((LLVMSimpleMemoryInvariant)value).getPointedToValue();
                        assert (
                            other_to.equals(this_to)
                            || (replacements.containsKey(other_to) && this_to.equals(replacements.get(other_to)))
                        ) : "Replacement of references would lead to inconsistent heap information!";
                    }
                } else if (otherVal instanceof LLVMIntervalMemoryInvariant){
                    // there are no references used in IntervalInvariants, no problem here
                    // TODO I don't think the comment above is true
                } else if (otherVal instanceof LLVMCombinedMemoryInvariant){
                    if (value instanceof LLVMCombinedMemoryInvariant) {
                        for (Map.Entry<BigInteger,LLVMMemoryInvariant> inv : ((LLVMCombinedMemoryInvariant)otherVal).getInvariants().entrySet()) {
                            if (inv instanceof LLVMComplexMemoryInvariant) {
                                LLVMSimpleTerm invFirst = ((LLVMComplexMemoryInvariant)inv).getFirstValue();
                                LLVMSimpleTerm invLast = ((LLVMComplexMemoryInvariant)inv).getLastValue();
                                LLVMMemoryInvariant thisInv = ((LLVMCombinedMemoryInvariant)value).getInvariantWithOffset(inv.getKey());
                                if (thisInv instanceof LLVMComplexMemoryInvariant) {
                                    LLVMSimpleTerm thisInvFirst = ((LLVMComplexMemoryInvariant)thisInv).getFirstValue();
                                    assert (
                                        invFirst.equals(thisInvFirst)
                                        || (replacements.containsKey(invFirst) && thisInvFirst.equals(replacements.get(invFirst)))
                                    ) : "Replacement of references would lead to inconsistent heap information!";
                                    LLVMSimpleTerm thisInvLast = ((LLVMComplexMemoryInvariant)thisInv).getLastValue();
                                    assert (
                                        invLast.equals(thisInvLast)
                                        || (replacements.containsKey(invLast) && thisInvLast.equals(replacements.get(invLast)))
                                    ) : "Replacement of references would lead to inconsistent heap information!";
                                }
                            }
                            if (inv instanceof LLVMSimpleMemoryInvariant) {
                                LLVMSimpleTerm invTo = ((LLVMSimpleMemoryInvariant)inv).getPointedToValue();
                                LLVMMemoryInvariant thisInv = ((LLVMCombinedMemoryInvariant)value).getInvariantWithOffset(inv.getKey());
                                if (thisInv instanceof LLVMSimpleMemoryInvariant) {
                                    LLVMSimpleTerm thisTo = ((LLVMSimpleMemoryInvariant)thisInv).getPointedToValue();
                                    assert (
                                        invTo.equals(thisTo)
                                        || (replacements.containsKey(invTo) && thisTo.equals(replacements.get(invTo)))
                                    ) : "Replacement of references would lead to inconsistent heap information!";
                                }
                            }
                        }
                    }
                } else if (otherVal == null) {
                    // everything is fine, no conflicting heap ranges
                } else {
                    throw new IllegalStateException("unknown invariant type");
                }
            }
            newMemory.put(newPair, value);
        }
        // Relations
        LLVMHeuristicRelationSet newRels = new LLVMHeuristicRelationSet(this.getRelations());
        newRels.applySubstitution(replacements);
        Iterator<LLVMHeuristicRelation> relIt = newRels.iterator();
        while (relIt.hasNext()) {
            LLVMHeuristicRelation rel = relIt.next();
            LLVMHeuristicTerm lhs = rel.getLhs();
            LLVMHeuristicTerm rhs = rel.getRhs();
            if (lhs instanceof LLVMHeuristicConstRef && rhs instanceof LLVMHeuristicConstRef) {
                relIt.remove();
                if(!LLVMHeuristicIntegerState.checkRelationOnConstants(
                            ((LLVMHeuristicConstRef)lhs).getIntegerValue(),
                            rel.getHeuristicRelationType(),
                            ((LLVMHeuristicConstRef)rhs).getIntegerValue()
                        )
                    ) {
                	throw new InconsistentStateException(getIntegerState(), rel);
                }
                
            }
        }
        // Values:
        Map<LLVMHeuristicVariable, LLVMValue> newVals =
            new LinkedHashMap<LLVMHeuristicVariable, LLVMValue>(this.getValues());
        for (Map.Entry<LLVMHeuristicVariable, LLVMHeuristicVariable> repEntry : replacements.entrySet()) {
            LLVMHeuristicVariable repKey = repEntry.getKey();
            LLVMHeuristicVariable repVal = repEntry.getValue();
            LLVMValue keyValue = LLVMHeuristicState.getValue(repKey, newVals);
            LLVMValue valValue = LLVMHeuristicState.getValue(repVal, newVals);
            if (keyValue != null) {
                if (valValue == null) {
                    newVals.put(repVal, keyValue);
                } else {
                    try {
                        LLVMValue intersectVal =
                            keyValue.getThisAsAbstractBoundedInt().intersect(valValue.getThisAsAbstractBoundedInt());
                        if (this.isPossiblyTrapValue(repKey) && this.isPossiblyTrapValue(repVal)) {
                            throw new IllegalStateException("Too many trap values!");
                        }
                        newVals.put(repVal, intersectVal);
                    } catch (IntersectionFailException e) {
                        throw
                            new InconsistentStateException(getIntegerState(), getRelationFactory().equalTo(repKey, repVal));
                    }
                }
                newVals.remove(repKey);
            }
        }
        // trap values
        Map<LLVMSymbolicVariable, LLVMTrapCondition> newTrapValues =
            new LinkedHashMap<LLVMSymbolicVariable, LLVMTrapCondition>();
        for (Map.Entry<LLVMSymbolicVariable, LLVMTrapCondition> entry : this.getTrapValues().entrySet()) {
            if (replacements.containsKey(entry.getKey())) {
                newTrapValues.put(
                    replacements.get(entry.getKey()),
                    (LLVMTrapCondition)entry.getValue().applySubstitution(replacements)
                );
            } else {
                newTrapValues.put(entry.getKey(), (LLVMTrapCondition)entry.getValue().applySubstitution(replacements));
            }
        }
        // allocated memory
        List<LLVMAllocation> newAllocMem = new ArrayList<LLVMAllocation>(this.getAllocations());
        for (int i = 0; i < newAllocMem.size(); i++) {
            LLVMAllocation pair = newAllocMem.get(i);
            if (replacements.containsKey(pair.x)) {
                if (replacements.containsKey(pair.y)) {
                    newAllocMem.set(i, new LLVMAllocation(replacements.get(pair.x), replacements.get(pair.y)));
                } else {
                    newAllocMem.set(i, new LLVMAllocation(replacements.get(pair.x), pair.y));
                }
            } else if (replacements.containsKey(pair.y)) {
                newAllocMem.set(i, new LLVMAllocation(pair.x, replacements.get(pair.y)));
            }
        }
        Map<LLVMHeuristicVariable, Integer> newAssocs =
            new LinkedHashMap<LLVMHeuristicVariable, Integer>(this.getAssociations());
        Map<LLVMHeuristicVariable, BigInteger> newAssocOffsets =
            new LinkedHashMap<LLVMHeuristicVariable, BigInteger>(this.getAssociationOffsets());
        for (LLVMHeuristicVariable associated : this.getAssociations().keySet()) {
            if (!replacements.containsKey(associated)) {
                continue;
            }
            LLVMHeuristicVariable replacementRef = replacements.get(associated);
            if (Globals.useAssertions && !LLVMDebuggingFlags.SV_COMP_MODE) {
                if (newAssocs.containsKey(replacementRef)) {
                    assert (newAssocs.get(associated).equals(newAssocs.get(replacementRef))) :
                        "Trying to replace references from different allocated areas!";
                }
            }
            newAssocs.put(replacementRef, newAssocs.remove(associated));
            BigInteger offset = newAssocOffsets.get(replacementRef);
            newAssocOffsets.put(
                replacementRef,
                offset == null ? newAssocOffsets.remove(associated) : offset.max(newAssocOffsets.remove(associated))
            );
        }
        Deque<LLVMReturnInformation> newCallStack = new ArrayDeque<LLVMReturnInformation>();
        for (LLVMReturnInformation inf : this.getCallStack()) {
            Map<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> newVarFunc =
                new LinkedHashMap<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>>(inf.getProgramVariables());
            for (Map.Entry<String, ImmutablePair<LLVMSymbolicVariable, LLVMType>> e : newVarFunc.entrySet()) {
                ImmutablePair<LLVMSymbolicVariable, LLVMType> val = e.getValue();
                if (replacements.containsKey(val.x)) {
                    e.setValue(new ImmutablePair<LLVMSymbolicVariable, LLVMType>(replacements.get(val.x), val.y));
                }
            }
            newCallStack.add(
                new LLVMReturnInformation(
                    ImmutableCreator.create(newVarFunc),
                    inf.getProgPos(),
                    inf.getAllocationsInFunction()
                )
            );
        }
        Set<ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>> newUnequalCache =
            new LinkedHashSet<ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>>();
        for (ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef> unequal : this.getUnequalCache()) {
            if (replacements.containsKey(unequal.x)) {
                if (replacements.containsKey(unequal.y)) {
                    LLVMHeuristicVariable repRef1 = replacements.get(unequal.x);
                    LLVMHeuristicVariable repRef2 = replacements.get(unequal.y);
                    if (repRef1 instanceof LLVMHeuristicVarRef && repRef2 instanceof LLVMHeuristicVarRef) {
                        newUnequalCache.add(
                            new ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>(
                                (LLVMHeuristicVarRef)repRef1,
                                (LLVMHeuristicVarRef)repRef2
                            )
                        );
                    }
                } else {
                    LLVMHeuristicVariable repRef1 = replacements.get(unequal.x);
                    if (repRef1 instanceof LLVMHeuristicVarRef) {
                        newUnequalCache.add(
                            new ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>(
                                (LLVMHeuristicVarRef)repRef1,
                                unequal.y
                            )
                        );
                    }
                }
            } else if (replacements.containsKey(unequal.y)) {
                LLVMHeuristicVariable repRef2 = replacements.get(unequal.y);
                if (repRef2 instanceof LLVMHeuristicVarRef) {
                    newUnequalCache.add(
                        new ImmutablePair<LLVMHeuristicVarRef, LLVMHeuristicVarRef>(
                            unequal.x,
                            (LLVMHeuristicVarRef)repRef2
                        )
                    );
                }
            } else {
                newUnequalCache.add(unequal);
            }
        }
        // initial heap references
        Map<Integer, LLVMHeuristicVariable> newInitHeapRefs =
            new LinkedHashMap<Integer, LLVMHeuristicVariable>(this.getInitialHeapAddresses());
        for (Map.Entry<Integer, LLVMHeuristicVariable> entry : newInitHeapRefs.entrySet()) {
            LLVMHeuristicVariable ref = entry.getValue();
            if (replacements.containsKey(ref)) {
                entry.setValue(replacements.get(ref));
            }
        }
        LLVMHeuristicState res =
            this.setProgramVariables(
                newVars
            ).setValues(
                newVals
            ).setMemory(
                newMemory
            ).setAllocatedMemoryForAlloca(
                newAllocMem,
                this.getAllocatedInCurrentFunctionFrameIndices()
            ).setAssociations(
                newAssocs,
                newAssocOffsets
            ).setCallStack(
                newCallStack
            ).setRelations(
                newRels
            ).setUnequalCache(
                newUnequalCache
            ).setInitialHeapAddresses(
                newInitHeapRefs
            ).setTrapValues(
                newTrapValues
            );
        // replace references by constants if values have shrunk to constants (they cannot - well, should not - be
        // equal as this should have been caught already
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> furtherReplacements =
            new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>();
        final LLVMHeuristicTermFactory termFactory = this.getRelationFactory().getTermFactory();
        for (Map.Entry<LLVMHeuristicVariable, LLVMValue> valEntry : newVals.entrySet()) {
            LLVMValue value = valEntry.getValue();
            if (value instanceof AbstractFloat) continue;
            AbstractBoundedInt val = value.getThisAsAbstractBoundedInt();
            if (val.isIntLiteral()) {
                LLVMHeuristicVariable valKey = valEntry.getKey();
                if (this.isPossiblyTrapValue(valKey)) {
                    throw new IllegalStateException("Trap value assignment to constant!");
                }
                LLVMHeuristicConstRef newVal = termFactory.constant(val.getIntLiteralValue());
                res = res.replaceSymbolicVariable(valKey, newVal);
                furtherReplacements.put(valKey, newVal);
            }
        }
        LLVMHeuristicRelationSet check;
        boolean again;
        Set<LLVMHeuristicVariable> valsChanged = new LinkedHashSet<LLVMHeuristicVariable>();
        do {
            check = new LLVMHeuristicRelationSet(res.getRelations());
            again = false;
            for (LLVMHeuristicRelation rel : check.getRelationsWithoutUndirectedInequalities()) {
                if (!rel.isSimple()) {
                    continue;
                }
                LLVMHeuristicVariable lhs = (LLVMHeuristicVariable)rel.getLhs();
                LLVMHeuristicVariable rhs = (LLVMHeuristicVariable)rel.getRhs();
                if (lhs instanceof LLVMHeuristicConstRef) {
                    if (rhs instanceof LLVMHeuristicConstRef) {
                        continue;
                    }
                    if (rel.isEquation()) {
                        res = res.replaceSymbolicVariable(rhs, lhs);
                        furtherReplacements.put(rhs, lhs);
                        again = true;
                        break;
                    } else {
                        LLVMValue value = res.getValue(rhs);
                        AbstractBoundedInt val = value.getThisAsAbstractBoundedInt();
                        IntervalBound lower = val.getLower();
                        BigInteger limit = ((LLVMHeuristicConstRef)lhs).getIntegerValue();
                        if (rel.isStrictInequality()) {
                            limit = limit.add(BigInteger.ONE);
                        }
                        if (lower.isFinite()) {
                            if (lower.getConstant().compareTo(limit) < 0) {
                            	AbstractBoundedInt afterLower = val.setLower(IntervalBound.create(limit));
                            	if(afterLower == null) {
                            		throw new InconsistentStateException(null, null);
                            	}
                                res = res.setValue(rhs, afterLower);
                                valsChanged.add(rhs);
                            } // else do nothing
                        } else {
                        	AbstractBoundedInt afterLower = val.setLower(IntervalBound.create(limit));
                        	if(afterLower == null) {
                        		throw new InconsistentStateException(null, null);
                        	}
                            res = res.setValue(rhs, afterLower);
                            valsChanged.add(rhs);
                        }
                    }
                } else if (rhs instanceof LLVMHeuristicConstRef) {
                    if (rel.isEquation()) {
                        res = res.replaceSymbolicVariable(lhs, rhs);
                        furtherReplacements.put(lhs, rhs);
                        again = true;
                        break;
                    } else {
                        LLVMValue value = res.getValue(lhs);
                        AbstractBoundedInt val = value.getThisAsAbstractBoundedInt();
                        IntervalBound upper = val.getUpper();
                        BigInteger limit = ((LLVMHeuristicConstRef)rhs).getIntegerValue();
                        if (rel.isStrictInequality()) {
                            limit = limit.subtract(BigInteger.ONE);
                        }
                        if (upper.isFinite()) {
                            if (upper.getConstant().compareTo(limit) > 0) {
                            	AbstractBoundedInt nVal = val.setUpper(IntervalBound.create(limit));
                            	if(nVal == null) {
                            		throw new InconsistentStateException(null, null);
                            	}
                                res = res.setValue(lhs, nVal);
                                valsChanged.add(lhs);
                            } // else do nothing
                        } else {
                            res = res.setValue(lhs, val.setUpper(IntervalBound.create(limit)));
                            valsChanged.add(lhs);
                        }
                    }
                }
            }
        } while (again);
        for (LLVMHeuristicVariable ref : valsChanged) {
            res = res.updateValuesAccordingToEquations(ref, new LLVMHeuristicRelationSet());
        }
        if (Globals.useAssertions) {
            for (Map.Entry<LLVMHeuristicVariable, LLVMHeuristicVariable> repEntry : furtherReplacements.entrySet()) {
                if (replacements.containsKey(repEntry.getKey())) {
                    LLVMHeuristicVariable val = replacements.get(repEntry.getKey());
                    if (furtherReplacements.containsKey(val)) {
                        assert (repEntry.getValue().equals(furtherReplacements.get(val))) :
                            "Inconsistent replacements detected!";
                    } else {
                        assert (repEntry.getValue().equals(val)) : "Inconsistent replacements detected!";
                    }
                }
            }
        }
        for (Map.Entry<LLVMHeuristicVariable, LLVMHeuristicVariable> entry : replacements.entrySet()) {
            LLVMHeuristicVariable ref = entry.getValue();
            if (furtherReplacements.containsKey(ref)) {
                entry.setValue(furtherReplacements.get(ref));
            }
        }
        LLVMHeuristicExpressionUtils.updateReplacements(replacements, furtherReplacements);
        return res;
    }

    /**
     * @param adjustedParam Have the values been adjusted?
     * @return This state where the adjusted flag has been set to the specified value.
     */
    private LLVMHeuristicState setAdjusted(boolean adjustedParam) {
        return this.setIntegerState(this.getIntegerState().setAdjusted(adjustedParam));
    }

    /**
     * @param cleanParam Are the relation clean?
     * @return This state where the clean flag has been set to the specified value.
     */
    private LLVMHeuristicState setClean(boolean cleanParam) {
        return this.setIntegerState(this.getIntegerState().setClean(cleanParam));
    }

    /**
     * @param var Some symbolic variable.
     * @return This state where we know that the specified variable is unequal to zero.
     */
    private LLVMHeuristicState unequalsZero(LLVMHeuristicVariable var) {
        if (var.isConcrete()) {
            if (var.isZero()) {
                return this;
            }
            throw new IllegalStateException("Tried to add contradictive relation!");
        }
        //TODO bounded?
        AbstractInt old = this.getValue(var).getThisAsAbstractInt();
        if (old.containsLiteral(BigInteger.ZERO)) {
            return this.setValue(var, old.removeZeroFromInteger());
        }
        return this;
    }

    /**
     * Attention: this method might yield tautological relations which must be cleaned thereafter!
     * @param ref1 Some reference.
     * @param ref2 Another reference.
     * @param replacements The replacements conducted.
     * @param shrinking The shrunk non-constant intervals.
     * @return The state resulting from unifying <code>ref1</code> and <code>ref2</code>.
     */
    private LLVMHeuristicState unifyReferences(
        LLVMHeuristicVariable ref1,
        LLVMHeuristicVariable ref2,
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> replacements,
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> shrinking
    ) {
        LLVMReplacementResult repRes = this.unifySymbolicVariables(ref1, ref2);
        shrinking.keySet().removeAll(repRes.y.keySet());
        LLVMHeuristicExpressionUtils.updateReplacements(replacements, repRes.y);
        return repRes.x;
    }

    /**
     * Updates the old shrinking map by the new shrinking map and constructs a substitution from references to
     * constants according to abstract values shrunk to represent a single concrete value.
     * @param oldShrinking The old shrinking map.
     * @param newShrinking The new shrinking map.
     * @return A substitution from references to constants newly learned by the combination of the old and new
     *         shrinking.
     */
    private Map<LLVMHeuristicVariable, LLVMHeuristicVariable> updateShrinking(
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> oldShrinking,
        Map<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> newShrinking
    ) {
        final LLVMHeuristicTermFactory termFactory = this.getRelationFactory().getTermFactory();
        Map<LLVMHeuristicVariable, LLVMHeuristicVariable> substitution =
            new LinkedHashMap<LLVMHeuristicVariable, LLVMHeuristicVariable>();
        for (Map.Entry<LLVMHeuristicVariable, Pair<BigInteger, BigInteger>> entry : newShrinking.entrySet()) {
            LLVMHeuristicVariable key = entry.getKey();
            Pair<BigInteger, BigInteger> value = entry.getValue();
            if (value.x != null) {
                if (value.y != null) {
                    if (value.x.compareTo(value.y) == 0) {
                        substitution.put(key, termFactory.constant(value.x));
                        if (Globals.useAssertions) {
                            if (oldShrinking.containsKey(key)) {
                                Pair<BigInteger, BigInteger> old = oldShrinking.get(key);
                                if (old.x != null) {
                                    assert old.x.compareTo(value.x) <= 0 : "Inconsistent value update!";
                                }
                                if (old.y != null) {
                                    assert old.y.compareTo(value.x) >= 0 : "Inconsistent value update!";
                                }
                            }
                        }
                        oldShrinking.remove(key);
                    } else if (oldShrinking.containsKey(key)) {
                        Pair<BigInteger, BigInteger> old = oldShrinking.get(key);
                        if (old.x == null || old.x.compareTo(value.x) < 0) {
                            old.x = value.x;
                        }
                        if (old.y == null || old.y.compareTo(value.y) > 0) {
                            old.y = value.y;
                        }
                    } else {
                        oldShrinking.put(key, value);
                    }
                } else if (oldShrinking.containsKey(key)) {
                    Pair<BigInteger, BigInteger> old = oldShrinking.get(key);
                    if (old.x == null || old.x.compareTo(value.x) < 0) {
                        old.x = value.x;
                        if (old.y != null && old.y.compareTo(old.x) == 0) {
                            substitution.put(key, termFactory.constant(old.x));
                            oldShrinking.remove(key);
                        }
                    }
                } else {
                    oldShrinking.put(key, value);
                }
            } else if (value.y != null) {
                if (oldShrinking.containsKey(key)) {
                    Pair<BigInteger, BigInteger> old = oldShrinking.get(key);
                    if (old.y == null || old.y.compareTo(value.y) > 0) {
                        old.y = value.y;
                        if (old.x != null && old.x.compareTo(old.y) == 0) {
                            substitution.put(key, termFactory.constant(old.x));
                            oldShrinking.remove(key);
                        }
                    }
                } else {
                    oldShrinking.put(key, value);
                }
            }
        }
        return substitution;
    }

    /**
     * @param ref A reference.
     * @param value The value object for ref (may be a trap value).
     * @param val The value of ref as AbstractBoundedInt.
     * @param lower The lower bound of val.
     * @param upper The upper bound of val.
     * @param refOff The constant offset of one side of an equation holding ref as the only variable and just this
     *               constant offset in addition to that.
     * @param otherOff The other side of the equation just holding another variable and a constant offset.
     * @param changed The set of references whose values have been changed.
     * @param newRels The newly learned relations.
     * @return The state emerging from this state by updating the value of otherOff.x or ref and a flag indicating
     *         whether the value of ref has changed.
     */
    private Pair<LLVMHeuristicState, Boolean> updateValuesAccordingToSpecifiedEquation(
        LLVMHeuristicVariable ref,
        LLVMValue value,
        AbstractBoundedInt val,
        IntervalBound lower,
        IntervalBound upper,
        BigInteger refOff,
        Pair<LLVMHeuristicVariable, BigInteger> otherOff,
        Set<LLVMHeuristicVariable> changed,
        Set<LLVMHeuristicRelation> newRels
    ) {
        final LLVMHeuristicTermFactory termFactory = this.getRelationFactory().getTermFactory();
        // ref + refOff = otherOff.x + otherOff.y
        LLVMHeuristicState res = this;
        BigInteger offset = otherOff.y.subtract(refOff);
        // ref = otherOff.x + offset
        // TODO this statement might lead to a cast exception as soon as we have other values than integers
        LLVMValue otherValue = res.getValue(otherOff.x);
        AbstractBoundedInt otherVal = otherValue.getThisAsAbstractBoundedInt();
        if (Globals.useAssertions && LLVMDebuggingFlags.CHECK_INVARIANTS) {
            assert (otherVal != null) : "Found reference not occurring in the value function of this state!";
        }
        final LLVMHeuristicRelationFactory relationFactory = this.getRelationFactory();
        if (lower.isFinite()) {
            IntervalBound otherLower = otherVal.getLower();
            // otherOff.x >= otherLower
            // ref >= lower
            // otherOff.x + offset >= lower
            // otherOff.x >= lower - offset
            BigInteger newOtherLower = lower.getConstant().subtract(offset);
            if (otherLower.compareTo(newOtherLower) < 0) {
                otherVal = otherVal.setLower(IntervalBound.create(newOtherLower));
                if (otherVal == null) {
                    throw new IllegalStateException("Knowledge inconsistent!");
                }
                res = res.setValue(otherOff.x, otherVal);
                if (newRels != null) {
                    newRels.add(relationFactory.lessThanEquals(termFactory.constant(newOtherLower), otherOff.x));
                }
                changed.add(otherOff.x);
            } else if (otherLower.compareTo(newOtherLower) > 0) {
                // ref - offset >= otherLower
                // ref >= otherLower + offset
                BigInteger newLower = otherLower.getConstant().add(offset);
                LLVMValue nextVal = val.setLower(IntervalBound.create(newLower));
                if (nextVal == null) {
                    throw new IllegalStateException("Knowledge inconsistent!");
                }
                changed.add(ref);
                if (newRels != null) {
                    newRels.add(relationFactory.lessThanEquals(termFactory.constant(newLower), ref));
                }
                // we need to start again with this ref anyway
                return new Pair<LLVMHeuristicState, Boolean>(res.setValue(ref, nextVal), true);
            }
        }
        if (upper.isFinite()) {
            IntervalBound otherUpper = otherVal.getUpper();
            // otherOff.x <= otherUpper
            // ref <= upper
            // otherOff.x + offset <= upper
            // otherOff.x <= upper - offset
            BigInteger newOtherUpper = upper.getConstant().subtract(offset);
            if (otherUpper.compareTo(newOtherUpper) > 0) {
                otherVal = otherVal.setUpper(IntervalBound.create(newOtherUpper));
                if (otherVal == null) {
                    throw new InconsistentStateException(null,null);
                }
                res = res.setValue(otherOff.x, otherVal);
                if (newRels != null) {
                    newRels.add(relationFactory.lessThanEquals(otherOff.x, termFactory.constant(newOtherUpper)));
                }
                changed.add(otherOff.x);
            } else if (otherUpper.compareTo(newOtherUpper) < 0) {
                // ref - offset <= otherUpper
                // ref <= otherUpper + offset
                BigInteger newUpper = otherUpper.getConstant().add(offset);
                LLVMValue nextVal = val.setUpper(IntervalBound.create(newUpper));
                if (nextVal == null) {
                    throw new IllegalStateException("Knowledge inconsistent!");
                }
                changed.add(ref);
                if (newRels != null) {
                    newRels.add(relationFactory.lessThanEquals(ref, termFactory.constant(newUpper)));
                }
                // we need to start again with this ref anyway
                return new Pair<LLVMHeuristicState, Boolean>(res.setValue(ref, nextVal), true);
            }
        }
        return new Pair<LLVMHeuristicState, Boolean>(res, false);
    }
    
    @Override
    public LLVMAbstractState getCallStackAbstractedState(boolean removeNonLiveVariables, Abortion aborter) {
    	LLVMHeuristicState callAbstraction = this.setCallStack(new ArrayDeque<LLVMReturnInformation>(0));
    	callAbstraction = callAbstraction.flagAbstractRecursiveFunctionStart();
    	
    	ImmutableTreeSet<Integer> allStackAllocations = getAllStackAllocatedIndices();
    	
        
        LLVMAbstractState resultPriorToPostProcessing =  new LLVMHeuristicState(
        		callAbstraction.getModule(),
                allStackAllocations,
                callAbstraction.getProgramPosition(),
                callAbstraction.isRefined(),
                callAbstraction.getIntegerState(),
                callAbstraction.getTrapValues(),
                callAbstraction.isAbstractRecursiveFunctionStart(),
                callAbstraction.getAllocatedByMallocIndices(),
                null,
                null, //set this after call abstracting
                callAbstraction.getStrategyParamters()
                );
        
        return resultPriorToPostProcessing.postProcessAfterCallAbstraction(removeNonLiveVariables, aborter).x;
                

    }
    
    @Override
    public ImmutableSet<LLVMSymbolicVariable> getEquivalenceclassOfSymbolicVariable(LLVMSymbolicVariable var, Abortion aborter) {
    	//It is an invariant that no two symbolic variables of a heuristic state must be known to be equal
    		return ImmutableCreator.create(Collections.singleton(var));
    }
    
    
    /**
     * 
     * Removes all allocations and heap info which are not reachable by
     * using a program variable and dereferencing
     */
    public LLVMHeuristicState retainReachableAllocationsAndHeapInfo(Abortion aborter) {
    	Set<LLVMHeuristicVariable> reachableVars = getUsedReferences(false,false);
    	Set<LLVMAllocation> reachableAllocations = new LinkedHashSet<>();
    	Set<LLVMMemoryRange> reachableMemoryEntries = new LinkedHashSet<>();
    	
    	boolean changed = false;
    	do {
    		changed = false;
    		
    		for(LLVMAllocation alloc : getAllocations()) {
    			if(reachableAllocations.contains(alloc))
    				continue;
    			
    			boolean reachable = false;
    			for(LLVMMemoryRange reachRange : reachableMemoryEntries) {
    				Pair<LLVMAssociationIndex,LLVMAbstractState> assIndex = getAssociatedAllocationIndex(reachRange, aborter);
    				if(assIndex.x != null && assIndex.x.x != null) {
    					LLVMAllocation correspondingAlloc = getAllocations().get(assIndex.x.x);
    					if(correspondingAlloc.equals(alloc)) {
    						reachable = true;
    						break;
    					}
    				}
    				
    			}
    			
    			reachable |= reachableVars.contains(alloc.x) || reachableVars.contains(alloc.y);
    			if(reachable) {
    				if(alloc.x instanceof LLVMHeuristicVariable) {
    					changed |= reachableVars.add((LLVMHeuristicVariable) alloc.x);
    				}
    				
    				if(alloc.y instanceof LLVMHeuristicVariable) {
    					changed |= reachableVars.add((LLVMHeuristicVariable) alloc.y);
    				}
    				changed |= reachableAllocations.add(alloc);
    				
    			}
    		}
    		
    		for(Map.Entry<LLVMMemoryRange,LLVMMemoryInvariant> stateMemEntry : getMemory().entrySet()) {
    			LLVMMemoryRange stateRange = stateMemEntry.getKey();
    			Pair<LLVMAssociationIndex,LLVMAbstractState> assIndex = getAssociatedAllocationIndex(stateRange, aborter);
				
    			boolean reachable = false;
    			if(assIndex.x != null && assIndex.x.x != null) {
					LLVMAllocation correspondingAlloc = getAllocations().get(assIndex.x.x);
					if(reachableAllocations.contains(correspondingAlloc)) {
						reachable = true;
					}
				}
    			reachable |= reachableVars.contains(stateRange.getFromRef()) || reachableVars.contains(stateRange.getToRef());
    			if(reachable) {
    				if(stateRange.getFromRef() instanceof LLVMHeuristicVariable) {
    					changed |= reachableVars.add((LLVMHeuristicVariable) stateRange.getFromRef());
    				}
    				
    				if(stateRange.getToRef() instanceof LLVMHeuristicVariable) {
    					changed |= reachableVars.add((LLVMHeuristicVariable) stateRange.getToRef());
    				}
    				
    				LLVMMemoryInvariant entryInv = stateMemEntry.getValue();
    				Set<LLVMSymbolicVariable> invariantVariables = entryInv.getUsedReferences();
    				for(LLVMSymbolicVariable invVar : invariantVariables) {
    					if(invVar instanceof LLVMHeuristicVariable) {
    						changed |= reachableVars.add((LLVMHeuristicVariable) invVar);
    					}
    				}
    				
    				
    				changed |= reachableMemoryEntries.add(stateRange);
    			}
    		}
    		
    	} while(changed);
    	
    	
    	LLVMHeuristicState resultState = this;
    	Set<LLVMAllocation> unreachableAllocations = new LinkedHashSet<>(getAllocations());
    	unreachableAllocations.removeAll(reachableAllocations);
    	
    	Set<LLVMMemoryRange> unreachableMemoryEntries = new LinkedHashSet<>(getMemory().keySet());
    	unreachableMemoryEntries.removeAll(reachableMemoryEntries);
    	
    	for(LLVMAllocation unreachableAllocation : unreachableAllocations) {
    		List<LLVMAllocation> remainingAllocations = resultState.getAllocations();
    		resultState = (LLVMHeuristicState) resultState.removeAllocation(remainingAllocations.indexOf(unreachableAllocation), true, aborter);
    	}
    	

    	resultState = (LLVMHeuristicState) resultState.removeHeapAccesses(unreachableMemoryEntries);
    	
    	
    	return resultState;
    }
    
    public LLVMHeuristicState setVarToEntryStateVarsMap(ImmutableMap<LLVMSymbolicVariable,ImmutableSet<LLVMSymbolicVariable>> entryStateVarCorrespondenceMap) {
    	return
                new LLVMHeuristicState(
                    this.getModule(),
                    this.getAllocatedInCurrentFunctionFrameIndices(),
                    this.getProgramPosition(),
                    this.isRefined(),
                    this.getIntegerState(),
                    this.getTrapValues(),
                    this.isAbstractRecursiveFunctionStart(),
                    this.getAllocatedByMallocIndices(),
                    entryStateVarCorrespondenceMap,
                    this.getAllocationChangedSinceEntryStateMap(),
                    this.getStrategyParamters()
                );
    }
    
    public LLVMHeuristicState setAllocationChangedSinceEntryState(ImmutableMap<Integer,Boolean> allocationChangedSinceEntryState) {
    	return
                new LLVMHeuristicState(
                    this.getModule(),
                    this.getAllocatedInCurrentFunctionFrameIndices(),
                    this.getProgramPosition(),
                    this.isRefined(),
                    this.getIntegerState(),
                    this.getTrapValues(),
                    this.isAbstractRecursiveFunctionStart(),
                    this.getAllocatedByMallocIndices(),
                    this.getEntryStateVarCorrespondenceMap(),
                    allocationChangedSinceEntryState,
                    this.getStrategyParamters()
                );
    }
    
    

    /**
     * Class for allowing access to some protected methods outside the package or hierarchy. Do not use it unless you
     * know exactly what you are doing. In effect this actually makes access to these methods possible everywhere but
     * since this is more difficult than just calling the methods, it reduces the danger of accidentally misusing them.
     * @author cryingshadow
     * @version $Id$
     */
    public static abstract class ProtectionAnchor {

        /**
         * Call this method only with relations not encoding mere value changes!
         * @param state The original state.
         * @param rels The relations to set.
         * @return The original state where the relations have been set to the specified ones.
         */
        protected LLVMHeuristicState setRelations(LLVMHeuristicState state, Set<LLVMHeuristicRelation> rels) {
            return state.setRelations(rels);
        }

    }

    /**
     * Give a name to pairs of ImmutablePairs of Allocations and Integers.
     * @author cryingshadow
     * @version $Id$
     */
    private static class AllocationCandidate extends Pair<LLVMAllocation, Integer> {

        /**
         * For serialization.
         */
        private static final long serialVersionUID = 2465492739595980845L;

        /**
         * @param x The immutable pair of references.
         * @param y The integer.
         */
        public AllocationCandidate(LLVMAllocation x, Integer y) {
            super(x, y);
        }
    }

    /**
     * Comparator for pointer types based on their offset.
     * @author cryingshadow
     * @version $Id$
     */
    private static class LLVMPointerTypeOffsetComparator implements Comparator<LLVMPointerType> {

        @Override
        public int compare(LLVMPointerType o1, LLVMPointerType o2) {
            return o1.toOffset().compareTo(o2.toOffset());
        }

    }

}
