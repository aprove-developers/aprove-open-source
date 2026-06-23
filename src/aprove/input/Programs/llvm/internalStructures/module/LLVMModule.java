package aprove.input.Programs.llvm.internalStructures.module;

import java.util.*;
import java.util.Map.Entry;
import java.util.stream.Collectors;

import org.json.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.utils.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.JSON.*;
import immutables.*;

/**
 * This class contains all parsed data of an LLVM program. It will be
 * constructed of the LLVMParseModule, which contains the crude LLVM program
 * built by the LLVM parser.
 *
 * Each LLVM program consists of function definitions, function declarations,
 * global variables and type definitions. Each function definition contains blocks
 * which finally consist of instructions.
 *
 * @author Janine Repke, Peter Schneider-Kamp, cryingshadow
 *
 * TODO better documentation of fields and methods
 */
public class LLVMModule implements Immutable, Exportable, JSONExport, LLVMIRExport {

    /**
     * @param decls The functions.
     * @return All program positions in the specified functions.
     */
    public static Set<LLVMProgramPosition> getAllPositions(Collection<? extends LLVMFnDeclaration> decls) {
        Set<LLVMProgramPosition> res = new LinkedHashSet<LLVMProgramPosition>();
        for (LLVMFnDeclaration decl : decls) {
            decl.collectAllPositions(res);
        }
        return res;
    }

    /**
     * @param globalVariables A collection of names of global variables.
     * @param functions A collection of functions.
     * @return A set of all program variable names occurring in the specified collections.
     */
    public static Set<String> getAllProgramVariableNames(
        Collection<String> globalVariables,
        Collection<? extends LLVMFnDeclaration> functions
    ) {
        Set<String> res = new LinkedHashSet<String>(globalVariables);
        for (LLVMFnDeclaration decl : functions) {
            decl.collectAllProgramVariableNames(res);
        }
        return res;
    }

    private static int computeAlignment(int size, String dataLayout) {
        // the relevant part of the layout string is of the form "i<size>:abiAlignment:"
        int numberOfDigits = ((int) Math.log10(size)) + 1;
        int indexStart = dataLayout.indexOf("i" + size + ":") + 2 + numberOfDigits;
        int indexEnd = dataLayout.indexOf('-', indexStart);
        if (indexStart > 1 + numberOfDigits) {
            // type is an exact match in data layout
            String iInfoAsString = dataLayout.substring(indexStart, indexEnd);
            String[] iInfo = iInfoAsString.split(":");
            return Integer.parseInt(iInfo[0]);
        } else {
            // we have to search for the smallest integer type which is larger than size
            // integer type information is of the form i:<size>:<alignment>
            ArrayList<Pair<Integer,Integer>> sizes = new ArrayList<>();
            indexStart = dataLayout.indexOf("i") + 1;
            indexEnd = dataLayout.indexOf('-', indexStart);
            String restOfDataLayout = dataLayout.substring(indexStart);
            while (indexStart > 0) {
                String iInfoAsString = restOfDataLayout.substring(0, indexEnd - indexStart);
                String[] iInfo = iInfoAsString.split(":");
                if (iInfo.length >= 1) {
                    sizes.add(new Pair<Integer,Integer>(Integer.parseInt(iInfo[0]),Integer.parseInt(iInfo[1])));
                }
                indexStart = restOfDataLayout.indexOf("i") + 1;
                indexEnd = restOfDataLayout.indexOf('-', indexStart);
                restOfDataLayout = restOfDataLayout.substring(indexStart);
            }
            // check native integer information of the form n(:<size>)*
            int nStart = dataLayout.indexOf("n") + 1;
            int nEnd = dataLayout.indexOf('-', nStart);
            String nArea = dataLayout.substring(nStart, nEnd);
            String[] nSizesAsStrings = nArea.split(":");
            for (String s : nSizesAsStrings) {
                sizes.add(new Pair<Integer,Integer>(Integer.parseInt(s),Integer.parseInt(s)));
            }
            // find the smallest match (i.e., the alignment of the smallest integer type larger than size or if
            // there is none, the alignment of the greatest integer type)
            Pair<Integer,Integer> next = sizes.get(0);
            int smallestMatchSize = next.getKey();
            int smallestMatchAlignment = next.getValue();
            int i = 1;
            while (next.getKey() != size && i < sizes.size()) {
                next = sizes.get(i);
                if (smallestMatchSize < size && next.getKey() > smallestMatchSize) {
                    smallestMatchSize = next.getKey();
                    smallestMatchAlignment = next.getValue();
                }
                if (smallestMatchSize > size && next.getKey() < smallestMatchSize && next.getKey() >= size) {
                    smallestMatchSize = next.getKey();
                    smallestMatchAlignment = next.getValue();
                }
                i++;
            }
            return smallestMatchAlignment;
        }
    }

    /**
     * @param dataLayout The dataLayout that specifies the integer alignment.
     * @return The size of an i16 used throughout the module.
     */
    private static int computeI16AlignmentFromDataLayout(String dataLayout) {
        return LLVMModule.computeAlignment(16, dataLayout);
    }

    /**
     * @param dataLayout The dataLayout that specifies the integer alignment.
     * @return The size of an i1 used throughout the module.
     */
    private static int computeI1AlignmentFromDataLayout(String dataLayout) {
        return LLVMModule.computeAlignment(1, dataLayout);
    }

    /**
     * @param dataLayout The dataLayout that specifies the integer alignment.
     * @return The size of an i32 used throughout the module.
     */
    private static int computeI32AlignmentFromDataLayout(String dataLayout) {
        return LLVMModule.computeAlignment(32, dataLayout);
    }

    /**
     * @param dataLayout The dataLayout that specifies the integer alignment.
     * @return The size of an i64 used throughout the module.
     */
    private static int computeI64AlignmentFromDataLayout(String dataLayout) {
        return LLVMModule.computeAlignment(64, dataLayout);
    }

    /**
     * @param dataLayout The dataLayout that specifies the integer alignment.
     * @return The size of an i8 used throughout the module.
     */
    private static int computeI8AlignmentFromDataLayout(String dataLayout) {
        return LLVMModule.computeAlignment(8, dataLayout);
    }

    /**
     * @param dataLayout The dataLayout that specifies the integer alignment.
     * @return The size of an i64 used throughout the module.
     */
    private static int computePointerAlignmentFromDataLayout(String dataLayout, String machine) {
        // the relevant part of the layout string has the form "p:size:abiAlignment" where the terminator is ":" or "-"
        int indexStart = dataLayout.indexOf("p:") + 2;
        if (indexStart > 1) {
            indexStart = dataLayout.indexOf(':', indexStart) + 1;
            if (dataLayout.substring(indexStart, indexStart + 1).equals("m")) {
                // We have an M1 processor. The size starts after the "m".
                indexStart++;
            }
            int indexEnd = Math.min(dataLayout.indexOf(':', indexStart), dataLayout.indexOf('-', indexStart));
            String i64Alignment = dataLayout.substring(indexStart, indexEnd);
            return Integer.parseInt(i64Alignment);
        } else {
            indexStart = machine.indexOf("x86_") + 4;
            if (machine.substring(indexStart, indexStart + 1).equals("m")) {
                // We have an M1 processor. The size starts after the "m".
                indexStart++;
            }
            int indexEnd = machine.indexOf('-', indexStart);
            String i64Alignment = machine.substring(indexStart, indexEnd);
            return Integer.parseInt(i64Alignment);
        }
    }

    /**
     * the set of program variables that we assume to point to unsigned values in the C program
     */
    private final ImmutableSet<Pair<String,String>> addressesToUnsignedBitvectorVariables;

    /**
     * alias definitions (the String mapping is redundant, but allows better search)
     */
    private final ImmutableMap<String, LLVMAliasDefinition> aliasDefinitions;

    /**
     * the layout specification
     */
    private final String dataLayout;

    /**
     * the debug information
     */
    private final ImmutableMap<Integer, LLVMDebugInformation> debugInformation;

    /**
     * function declarations and definitions (which are split in blocks and the blocks contain the instructions)
     * (the String mapping is redundant, but allows better search)
     */
    private final ImmutableMap<String, LLVMFnDeclaration> fnDeclarations;

    /**
     * the alignment of an i16
     */
    private final int i16Alignment;

    /**
     * the alignment of an i1
     */
    private final int i1Alignment;

    /**
     * the alignment of an i32
     */
    private final int i32Alignment;

    /**
     * the alignment of an i64
     */
    private final int i64Alignment;

    /**
     * the alignment of an i8
     */
    private final int i8Alignment;

    /**
     * The live variables.
     */
    private final ImmutableMap<LLVMProgramPosition, ImmutableSet<String>> liveVariables;

    /**
     * the target machine
     */
    private final String machine;

    private final Graph<LLVMProgramPosition, String> controlFlowGraph;

    private final static LLVMInstructionGraphNodeObjectCreator<LLVMProgramPosition> creator =
        new LLVMInstructionGraphNodeObjectCreator<LLVMProgramPosition>() {

        @Override
        public LLVMProgramPosition create(LLVMModule prog, LLVMProgramPosition pos) {
            return new LLVMProgramPosition(pos.getFunction(), pos.getBlock(), pos.getLine());
        }

    };

    /**
     * the alignment of a pointer
     */
    private final int pointerAlignment;

    /**
     * the size of a pointer
     */
    private final int pointerSize;

    /**
     * the set of program specific relations
     */
    private final ImmutableSet<LLVMLiteralRelation> programLiteralRelations;

    /**
     * the set of program specific relations
     */
    private final ImmutableSet<LLVMRelation> programReferenceRelations;

    /**
     * Stores sufficient conditions for positions under which they must reach a ret instruction. If a position is
     * mapped to an empty set, we do not know a sufficient condition. If otherwise a state satisfies one set of
     * relations, it must reach a ret instruction from its position. This information is used to avoid generalizations
     * with states that must reach a ret instruction.
     */
    private final ImmutableMap<LLVMProgramPosition, ImmutableSet<ImmutableSet<IntegerRelation>>> returnConditions;

    /**
     * type definitions
     */
    private final ImmutableMap<String, LLVMType> typeDefinitions;

    /**
     * the set of program variables that we assume to be unsigned in the C program
     */
    private final ImmutableSet<Pair<String,String>> unsignedBitvectorVariables;

    /**
     * the set of program variables that are only used in unsigned comparisons
     */
    private final ImmutableSet<Pair<String,String>> unsignedUnboundedVariables;

    /**
     * The set of (function name, pointer/alloca variable name) pairs for which the C source declared the pointed-to
     * variable as an unsigned integer type. This is recovered from the debug metadata (llvm.dbg.declare +
     * DILocalVariable + DIBasicType) and is used to seed the unsigned variable sets. It is authoritative because it
     * stems from the actual C type rather than from a heuristic over comparison operators.
     */
    private final ImmutableSet<Pair<String,String>> debugUnsignedAllocas;

    /**
     * variable definitions
     */
    private final ImmutableMap<String, LLVMGlobalVariable> variables;

    /**
     * @param aliases Alias definitions.
     * @param layout The layout specification.
     * @param declarations Function declarations and definitions (which are split in blocks and the blocks contain the
     *                     instructions).
     * @param machineParam The target machine.
     * @param types Type definitions.
     * @param globalVars Global variable definitions.
     * @param liveVariablesParam Map from program positions to live variables.
     * @param returnConditionsParam Map from program positions to return conditions.
     * @param pointerSizeParam The size of pointers.
     */
    public LLVMModule(
        ImmutableMap<String, LLVMAliasDefinition> aliases,
        String layout,
        ImmutableMap<Integer, LLVMDebugInformation> debugInfo,
        ImmutableMap<String, LLVMFnDeclaration> declarations,
        String machineParam,
        ImmutableMap<String, LLVMType> types,
        ImmutableMap<String, LLVMGlobalVariable> globalVars,
        ImmutableSet<LLVMRelation> programRefRelations,
        ImmutableMap<LLVMProgramPosition, ImmutableSet<String>> liveVariablesParam,
        ImmutableMap<LLVMProgramPosition, ImmutableSet<ImmutableSet<IntegerRelation>>> returnConditionsParam,
        ImmutableSet<Pair<String,String>> debugUnsignedAllocasParam,
        int pointerSizeParam
    ) {
        this.aliasDefinitions = aliases;
        this.dataLayout = layout;
        this.debugInformation = debugInfo;
        this.debugUnsignedAllocas =
            debugUnsignedAllocasParam == null
                ? ImmutableCreator.create(new LinkedHashSet<Pair<String,String>>())
                : debugUnsignedAllocasParam;
        this.fnDeclarations = declarations;
        this.pointerSize = pointerSizeParam;
        this.i1Alignment = LLVMModule.computeI1AlignmentFromDataLayout(this.dataLayout);
        this.i8Alignment = LLVMModule.computeI8AlignmentFromDataLayout(this.dataLayout);
        this.i16Alignment = LLVMModule.computeI16AlignmentFromDataLayout(this.dataLayout);
        this.i32Alignment = LLVMModule.computeI32AlignmentFromDataLayout(this.dataLayout);
        this.i64Alignment = LLVMModule.computeI64AlignmentFromDataLayout(this.dataLayout);
        this.machine = machineParam;
        this.pointerAlignment = LLVMModule.computePointerAlignmentFromDataLayout(this.dataLayout, machineParam);
        this.programLiteralRelations = this.computeProgramLiteralRelations();
        this.programReferenceRelations = programRefRelations;
        this.typeDefinitions = types;
        Pair<ImmutableSet<Pair<String,String>>,ImmutableSet<Pair<String,String>>> pair = this.computeUnsignedBitvectorVariables();
        this.unsignedBitvectorVariables = pair.x;
        this.addressesToUnsignedBitvectorVariables = pair.y;
        this.unsignedUnboundedVariables = this.computeUnsignedUnboundedVariables();
        this.variables = globalVars;
        this.liveVariables = liveVariablesParam;
        this.returnConditions = returnConditionsParam;
        this.controlFlowGraph = this.computeInstructionGraph(creator);
    }

    /**
     * @param tmaker A factory to create suitable objects of type T given a program position and a module.
     * @return The instruction graph based on the specified factory for the node objects.
     */
    public <T> Graph<T, String> computeInstructionGraph(LLVMInstructionGraphNodeObjectCreator<T> tmaker) {
        Graph<T, String> instructionGraph = new Graph<T, String>();
        Set<LLVMProgramPosition> poss = this.getAllPositions();
        Map<LLVMProgramPosition, Node<T>> pos2node = new LinkedHashMap<LLVMProgramPosition, Node<T>>();
        for (LLVMProgramPosition pos : poss) {
            Node<T> node = new Node<T>(tmaker.create(this, pos));
            pos2node.put(pos, node);
            instructionGraph.addNode(node);
        }
        for (LLVMProgramPosition pos : poss) {
            Node<T> fromNode = pos2node.get(pos);
            for (LLVMProgramPosition successor : this.getInstruction(pos).getSuccessors(pos, this)) {
                if (Globals.useAssertions) {
                    assert this.getInstruction(successor) != null;
                }
                instructionGraph.addEdge(fromNode, pos2node.get(successor), pos.y);
            }
        }
        return instructionGraph;
    }

    /**
     * @return A set of relations that might be interesting for further analysis of the specified module.
     *         These relations may be used to imply new relations when merging two states.
     */
    public ImmutableSet<LLVMLiteralRelation> computeProgramLiteralRelations() {
        LinkedHashSet<LLVMLiteralRelation> res = new LinkedHashSet<LLVMLiteralRelation>();
        for (LLVMFnDeclaration decl : this.fnDeclarations.values()) {
            if (decl instanceof LLVMFnDefinition) {
                LLVMFnDefinition def = (LLVMFnDefinition) decl;
                for (LLVMBasicBlock block : def.getBlocks().values()) {
                    for (LLVMInstruction instruction : block.getInstructions()) {
                        LLVMLiteralRelation rel = instruction.computeRelation();
                        if (rel != null && !(rel.getLhs() instanceof LLVMNullLiteral) && !(rel.getRhs() instanceof LLVMNullLiteral)) {
                            res.add(rel);
                        }
                    }
                }
            }
        }
        return ImmutableCreator.create(res);
    }

    /**
     * @param params Strategy parameters.
     * @return This LLVM module where the return conditions are updated.
     */
    public LLVMModule computeReturnConditions(LLVMParameters params) {
        Map<LLVMProgramPosition, ImmutableSet<ImmutableSet<IntegerRelation>>> res =
            new LinkedHashMap<LLVMProgramPosition, ImmutableSet<ImmutableSet<IntegerRelation>>>();
        Graph<RetCond, String> instructionGraph =
            this.computeInstructionGraph(
                new LLVMInstructionGraphNodeObjectCreator<RetCond>(){

                    @Override
                    public RetCond create(LLVMModule program, LLVMProgramPosition pos) {
                        return new RetCond(
                            pos,
                            program.getInstruction(pos),
                            new LinkedHashSet<Pair<IntegerRelationSet, List<String>>>()
                        );
                    }

                }
            );
        // all returns must definitely reach themselves
        for (RetCond cond : instructionGraph.getNodeObjects()) {
            if (cond.y instanceof LLVMRetInstruction) {
                cond.z.add(
                    new Pair<IntegerRelationSet, List<String>>(
                        new IntegerRelationSet(),
                        Collections.<String>emptyList()
                    )
                );
            }
        }
        // perform backwards analysis (adding return conditions based on the ones of successors)
        SCCGraph<RetCond, String> sccGraph =
            new SCCGraph<RetCond, String>(instructionGraph, false, false);
        for (Cycle<RetCond> rank : sccGraph.getRankedSCCs()) {
            boolean changed;
            do {
                changed = false;
                for (Node<RetCond> node : rank) {
                    RetCond cond = node.getObject();
                    for (Node<RetCond> succ : instructionGraph.getOut(node)) {
                        RetCond succCond = succ.getObject();
                        changed |= cond.z.addAll(cond.y.computeReturnConditions(succCond.x, succCond.z, params));
                    }
                }
            } while (changed);
        }
        // now determine the mapping
        for (RetCond cond : instructionGraph.getNodeObjects()) {
            Set<ImmutableSet<IntegerRelation>> nextSet = new LinkedHashSet<ImmutableSet<IntegerRelation>>();
            for (Pair<IntegerRelationSet, List<String>> pair : cond.z) {
                nextSet.add(ImmutableCreator.create(pair.x));
            }
            res.put(cond.x, ImmutableCreator.create(nextSet));
        }
        return this.setReturnConditions(res);
    }

    /**
     * @return The set of program variables that we represent as unsigned instead of signed bitvector variables,
     * and their addresses.
     */
    public Pair<ImmutableSet<Pair<String,String>>,ImmutableSet<Pair<String,String>>> computeUnsignedBitvectorVariables() {
        LinkedHashSet<Pair<String,String>> res = new LinkedHashSet<Pair<String,String>>(computeUnsignedUnboundedVariables());
        // seed with the source signedness recovered from the debug metadata (authoritative C type information) so that
        // it is propagated through the fixpoint below
        this.addDebugUnsignedValues(res);
        LinkedHashSet<Pair<String,String>> resOld = null;
        LinkedHashSet<Pair<String,String>> addressesWithUnsignedValues = new LinkedHashSet<Pair<String,String>>();
        LinkedHashSet<Pair<String,String>> addressesWithUnsignedValuesOld = null;
        // collect variables that appear unsigned to us
        while (!(res.equals(resOld) && addressesWithUnsignedValues.equals(addressesWithUnsignedValuesOld))) {
            resOld = (LinkedHashSet<Pair<String,String>>) res.clone();
            addressesWithUnsignedValuesOld = (LinkedHashSet<Pair<String,String>>) addressesWithUnsignedValues.clone();
            for (Entry<String, LLVMFnDeclaration> decl : this.fnDeclarations.entrySet()) {
                if (decl.getValue() instanceof LLVMFnDefinition) {
                    LLVMFnDefinition def = (LLVMFnDefinition) decl.getValue();
                    for (LLVMBasicBlock block : def.getBlocks().values()) {
                        for (LLVMInstruction instruction : block.getInstructions()) {
                            if (instruction instanceof LLVMICmpInstruction && ((LLVMICmpInstruction) instruction).isSignNeutral()) {
                                for (LLVMLiteral lit : ((LLVMICmpInstruction) instruction).getOperands()) {
                                    if (lit instanceof LLVMVariableLiteral && res.contains(new Pair<String,String>(decl.getKey(),((LLVMVariableLiteral) lit).getName()))) {
                                        for (String operand : ((LLVMICmpInstruction) instruction).getOperandNames()) {
                                            res.add(new Pair<String,String>(decl.getKey(),operand));
                                        }
                                    }
                                }
                            }
                            if (instruction instanceof LLVMBinaryInstruction) {
                                LLVMBinaryInstruction binInst = (LLVMBinaryInstruction) instruction;
                                LLVMVariableLiteral identifier = binInst.getIdentifier();
                                if (binInst.seemsUnsigned()) {
                                    res.add(new Pair<String,String>(decl.getKey(),identifier.getName()));
                                    for (String operand : binInst.getOperandNames()) {
                                        res.add(new Pair<String,String>(decl.getKey(),operand));
                                    }
                                }
                                if (res.contains(new Pair<String,String>(decl.getKey(),identifier.getName()))) {
                                    for (String operand : binInst.getOperandNames()) {
                                        res.add(new Pair<String,String>(decl.getKey(),operand));
                                    }
                                }
                                for (LLVMLiteral lit : binInst.getOperands()) {
                                    if (lit instanceof LLVMVariableLiteral && res.contains(new Pair<String,String>(decl.getKey(),((LLVMVariableLiteral) lit).getName()))) {
                                        res.add(new Pair<String,String>(decl.getKey(),identifier.getName()));
                                        for (String operand : binInst.getOperandNames()) {
                                            res.add(new Pair<String,String>(decl.getKey(),operand));
                                        }
                                    }
                                }
                            }
                            if (instruction instanceof LLVMConversionInstruction) {
                                LLVMConversionInstruction convInst = (LLVMConversionInstruction) instruction;
                                LLVMVariableLiteral identifier = convInst.getIdentifier();
                                if (convInst.seemsUnsigned()) {
                                    res.add(new Pair<String,String>(decl.getKey(),convInst.getOperandName()));
                                    res.add(new Pair<String,String>(decl.getKey(),convInst.getIdentifier().getName()));
                                }
                                if (res.contains(new Pair<String,String>(decl.getKey(),identifier.getName()))) {
                                    res.add(new Pair<String,String>(decl.getKey(),convInst.getOperandName()));
                                }
                                if (res.contains(new Pair<String,String>(decl.getKey(),convInst.getOperandName()))) {
                                    res.add(new Pair<String,String>(decl.getKey(),identifier.getName()));
                                }
                            }
                            if (instruction instanceof LLVMLoadInstruction) {
                                String loadedVar = ((LLVMLoadInstruction) instruction).getIdentifier().getName();
                                LLVMLiteral pointerLit = ((LLVMLoadInstruction) instruction).getAddressValue();
                                if (pointerLit instanceof LLVMVariableLiteral) {
                                    String pointerName = ((LLVMVariableLiteral) pointerLit).getName();
                                    // if this variable is already unsigned, update addressesWithUnsignedValues
                                    if (res.contains(new Pair<String,String>(decl.getKey(),loadedVar))) {
                                        addressesWithUnsignedValues.add(new Pair<String,String>(decl.getKey(),pointerName));
                                    }
                                    // if its address is used in unsigned context, mark this variable as unsigned
                                    if (addressesWithUnsignedValues.contains(new Pair<String,String>(decl.getKey(),pointerName))) {
                                        res.add(new Pair<String,String>(decl.getKey(),loadedVar));
                                    }
                                }
                            }
                            if (instruction instanceof LLVMStoreInstruction) {
                                LLVMLiteral storedLit = ((LLVMStoreInstruction) instruction).getStoredValue();
                                LLVMLiteral pointerLit = ((LLVMStoreInstruction) instruction).getAddressValue();
                                if (storedLit instanceof LLVMVariableLiteral && pointerLit instanceof LLVMVariableLiteral) {
                                    String storedVar = ((LLVMVariableLiteral) storedLit).getName();
                                    String pointerName = ((LLVMVariableLiteral) pointerLit).getName();
                                    // if this variable is already unsigned, update addressesWithUnsignedValues
                                    if (res.contains(new Pair<String,String>(decl.getKey(),storedVar))) {
                                        addressesWithUnsignedValues.add(new Pair<String,String>(decl.getKey(),pointerName));
                                    }
                                    // if its address is used in unsigned context, mark this variable as unsigned
                                    if (addressesWithUnsignedValues.contains(new Pair<String,String>(decl.getKey(),pointerName))) {
                                        res.add(new Pair<String,String>(decl.getKey(),storedVar));
                                    }
                                }

                            }
                            if (instruction instanceof LLVMPhiInstruction) {
                                // not yet implemented
                            }
                            if (instruction instanceof LLVMSelectInstruction) {
                                LLVMVariableLiteral identifier = ((LLVMSelectInstruction) instruction).getIdentifier();
                                if (res.contains(new Pair<String,String>(decl.getKey(),identifier.getName()))) {
                                    for (String valueName : ((LLVMSelectInstruction) instruction).getValueNames()) {
                                        res.add(new Pair<String,String>(decl.getKey(),valueName));
                                    }
                                }
                                for (LLVMLiteral lit : ((LLVMSelectInstruction) instruction).getValues()) {
                                    if (lit instanceof LLVMVariableLiteral && res.contains(new Pair<String,String>(decl.getKey(),((LLVMVariableLiteral) lit).getName()))) {
                                        res.add(new Pair<String,String>(decl.getKey(),identifier.getName()));
                                        for (String valueName : ((LLVMSelectInstruction) instruction).getValueNames()) {
                                            res.add(new Pair<String,String>(decl.getKey(),valueName));
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        // now remove variables that - somewhere else - appear signed to us
        resOld = null;
        addressesWithUnsignedValuesOld = null;
        while (!(res.equals(resOld) && addressesWithUnsignedValues.equals(addressesWithUnsignedValuesOld))) {
            resOld = (LinkedHashSet<Pair<String,String>>) res.clone();
            addressesWithUnsignedValuesOld = (LinkedHashSet<Pair<String,String>>) addressesWithUnsignedValues.clone();
            for (Entry<String, LLVMFnDeclaration> decl : this.fnDeclarations.entrySet()) {
                if (decl.getValue() instanceof LLVMFnDefinition) {
                    LLVMFnDefinition def = (LLVMFnDefinition) decl.getValue();
                    for (LLVMBasicBlock block : def.getBlocks().values()) {
                        for (LLVMInstruction instruction : block.getInstructions()) {
                            if (instruction instanceof LLVMICmpInstruction) {
                                LLVMICmpInstruction icmp = (LLVMICmpInstruction) instruction;
                                if (icmp.isSigned()) {
                                    for (LLVMLiteral lit : icmp.getOperands()) {
                                        if (lit instanceof LLVMVariableLiteral) {
                                            res.remove(new Pair<String,String>(decl.getKey(),((LLVMVariableLiteral) lit).getName()));
                                        }
                                    }
                                }
                                for (LLVMLiteral lit : icmp.getOperands()) {
                                    if (lit instanceof LLVMVariableLiteral && !res.contains(new Pair<String,String>(decl.getKey(),((LLVMVariableLiteral) lit).getName()))) {
                                        for (String operand : ((LLVMICmpInstruction) instruction).getOperandNames()) {
                                            res.remove(new Pair<String,String>(decl.getKey(),operand));
                                        }
                                    }
                                }
                            }
                            if (instruction instanceof LLVMBinaryInstruction) {
                                LLVMBinaryInstruction binInst = (LLVMBinaryInstruction) instruction;
                                LLVMVariableLiteral identifier = binInst.getIdentifier();
                                if (binInst.seemsSigned()) {
                                    res.remove(new Pair<String,String>(decl.getKey(),binInst.getIdentifier().getName()));
                                    for (String operand : binInst.getOperandNames()) {
                                        res.remove(new Pair<String,String>(decl.getKey(),operand));
                                    }
                                }
                                if (!res.contains(new Pair<String,String>(decl.getKey(),identifier.getName()))) {
                                    for (String operand : binInst.getOperandNames()) {
                                        res.remove(new Pair<String,String>(decl.getKey(),operand));
                                    }
                                }
                                for (LLVMLiteral lit : binInst.getOperands()) {
                                    if (lit instanceof LLVMVariableLiteral && !res.contains(new Pair<String,String>(decl.getKey(),((LLVMVariableLiteral) lit).getName()))) {
                                        res.remove(new Pair<String,String>(decl.getKey(),identifier.getName()));
                                        for (String operand : binInst.getOperandNames()) {
                                            res.remove(new Pair<String,String>(decl.getKey(),operand));
                                        }
                                    }
                                }
                            }
                            if (instruction instanceof LLVMConversionInstruction) {
                                LLVMConversionInstruction convInst = (LLVMConversionInstruction) instruction;
                                LLVMVariableLiteral identifier = convInst.getIdentifier();
                                if (convInst.seemsSigned()) {
                                    res.remove(new Pair<String,String>(decl.getKey(),convInst.getOperandName()));
                                    res.remove(new Pair<String,String>(decl.getKey(),convInst.getIdentifier().getName()));
                                }
                                // ZEXT may convert unsigned variables to signed ones (or those used with nsw)
                                if (!convInst.isZEXT() && !res.contains(new Pair<String,String>(decl.getKey(),identifier.getName()))) {
                                    res.remove(new Pair<String,String>(decl.getKey(),convInst.getOperandName()));
                                }
                                // TRUNC may convert signed variables to unsigned ones
                                if (!convInst.isTRUNC() && !res.contains(new Pair<String,String>(decl.getKey(),convInst.getOperandName()))) {
                                    res.remove(new Pair<String,String>(decl.getKey(),identifier.getName()));
                                }
                            }
                            if (instruction instanceof LLVMLoadInstruction) {
                                String loadedVar = ((LLVMLoadInstruction) instruction).getIdentifier().getName();
                                LLVMLiteral pointerLit = ((LLVMLoadInstruction) instruction).getAddressValue();
                                if (pointerLit instanceof LLVMVariableLiteral) {
                                    String pointerName = ((LLVMVariableLiteral) pointerLit).getName();
                                    // if this variable is signed, update addressesWithUnsignedValues
                                    if (!res.contains(new Pair<String,String>(decl.getKey(),loadedVar))) {
                                        addressesWithUnsignedValues.remove(new Pair<String,String>(decl.getKey(),pointerName));
                                    }
                                    // if its address is used in signed context, mark this variable as signed
                                    if (!addressesWithUnsignedValues.contains(new Pair<String,String>(decl.getKey(),pointerName))) {
                                        res.remove(new Pair<String,String>(decl.getKey(),loadedVar));
                                    }
                                }
                            }
                            if (instruction instanceof LLVMStoreInstruction) {
                                LLVMLiteral storedLit = ((LLVMStoreInstruction) instruction).getStoredValue();
                                LLVMLiteral pointerLit = ((LLVMStoreInstruction) instruction).getAddressValue();
                                if (storedLit instanceof LLVMVariableLiteral && pointerLit instanceof LLVMVariableLiteral) {
                                    String storedVar = ((LLVMVariableLiteral) storedLit).getName();
                                    String pointerName = ((LLVMVariableLiteral) pointerLit).getName();
                                    // if this variable is signed, update addressesWithUnsignedValues
                                    if (!res.contains(new Pair<String,String>(decl.getKey(),storedVar))) {
                                        addressesWithUnsignedValues.remove(new Pair<String,String>(decl.getKey(),pointerName));
                                    }
                                    // if its address is used in signed context, mark this variable as signed
                                    if (!addressesWithUnsignedValues.contains(new Pair<String,String>(decl.getKey(),pointerName))) {
                                        res.remove(new Pair<String,String>(decl.getKey(),storedVar));
                                    }
                                }

                            }
                            if (instruction instanceof LLVMPhiInstruction) {
                                // not yet implemented
                            }
                            if (instruction instanceof LLVMSelectInstruction) {
                                LLVMVariableLiteral identifier = ((LLVMSelectInstruction) instruction).getIdentifier();
                                if (!res.contains(new Pair<String,String>(decl.getKey(),identifier.getName()))) {
                                    for (String valueName : ((LLVMSelectInstruction) instruction).getValueNames()) {
                                        res.remove(new Pair<String,String>(decl.getKey(),valueName));
                                    }
                                }
                                for (LLVMLiteral lit : ((LLVMSelectInstruction) instruction).getValues()) {
                                    if (lit instanceof LLVMVariableLiteral && !res.contains(new Pair<String,String>(decl.getKey(),((LLVMVariableLiteral) lit).getName()))) {
                                        res.remove(new Pair<String,String>(decl.getKey(),identifier.getName()));
                                        for (String valueName : ((LLVMSelectInstruction) instruction).getValueNames()) {
                                            res.remove(new Pair<String,String>(decl.getKey(),valueName));
                                        }
                                    }
                                }
                            }
                        }
                    }
                }
            }
        }
        return
            new Pair<ImmutableSet<Pair<String,String>>,ImmutableSet<Pair<String,String>>> (
                ImmutableCreator.create(res),
                ImmutableCreator.create(addressesWithUnsignedValues)
            );
    }

    /**
     * @return The set of program variables that are only used in unsigned but not signed comparisons.
     */
    public ImmutableSet<Pair<String,String>> computeUnsignedUnboundedVariables() {
        LinkedHashSet<Pair<String,String>> res = new LinkedHashSet<Pair<String,String>>();
        // collect all program variables used in at least one unsigned comparison
        for (Entry<String, LLVMFnDeclaration> decl : this.fnDeclarations.entrySet()) {
            if (decl.getValue() instanceof LLVMFnDefinition) {
                LLVMFnDefinition def = (LLVMFnDefinition) decl.getValue();
                for (LLVMBasicBlock block : def.getBlocks().values()) {
                    for (LLVMInstruction instruction : block.getInstructions()) {
                        if (instruction instanceof LLVMICmpInstruction && ((LLVMICmpInstruction) instruction).isUnsigned()) {
                            for (LLVMLiteral lit : ((LLVMICmpInstruction) instruction).getOperands()) {
                                if (lit instanceof LLVMVariableLiteral) {
                                    res.add(new Pair<String,String>(decl.getKey(),((LLVMVariableLiteral) lit).getName()));
                                }
                            }
                        }
                    }
                }
            }
        }
        // remove all variables used in signed comparisons
        for (Entry<String, LLVMFnDeclaration> decl : this.fnDeclarations.entrySet()) {
            if (decl.getValue() instanceof LLVMFnDefinition) {
                LLVMFnDefinition def = (LLVMFnDefinition) decl.getValue();
                for (LLVMBasicBlock block : def.getBlocks().values()) {
                    for (LLVMInstruction instruction : block.getInstructions()) {
                        if (instruction instanceof LLVMICmpInstruction && ((LLVMICmpInstruction) instruction).isSigned()) {
                            for (LLVMLiteral lit : ((LLVMICmpInstruction) instruction).getOperands()) {
                                if (lit instanceof LLVMVariableLiteral) {
                                    res.remove(new Pair<String,String>(decl.getKey(),((LLVMVariableLiteral) lit).getName()));
                                }
                            }
                        }
                    }
                }
            }
        }
        return ImmutableCreator.create(res);
    }

    /**
     * Seeds the specified set with the C source signedness recovered from the debug metadata: a value loaded from (or a
     * variable stored to) an alloca that holds an unsigned source variable is itself unsigned. This is only used for the
     * bitvector (bounded) integer representation.
     * @param res The set to seed (modified in place).
     */
    private void addDebugUnsignedValues(LinkedHashSet<Pair<String,String>> res) {
        if (this.debugUnsignedAllocas.isEmpty()) {
            return;
        }
        for (Entry<String, LLVMFnDeclaration> decl : this.fnDeclarations.entrySet()) {
            if (!(decl.getValue() instanceof LLVMFnDefinition)) {
                continue;
            }
            String funcName = decl.getKey();
            LLVMFnDefinition def = (LLVMFnDefinition) decl.getValue();
            for (LLVMBasicBlock block : def.getBlocks().values()) {
                for (LLVMInstruction instruction : block.getInstructions()) {
                    if (instruction instanceof LLVMLoadInstruction) {
                        LLVMLoadInstruction load = (LLVMLoadInstruction) instruction;
                        if (load.getAddressValue() instanceof LLVMVariableLiteral
                            && this.isDebugUnsignedAlloca(funcName, ((LLVMVariableLiteral) load.getAddressValue()).getName())) {
                            res.add(new Pair<String,String>(funcName, load.getIdentifier().getName()));
                        }
                    } else if (instruction instanceof LLVMStoreInstruction) {
                        LLVMStoreInstruction store = (LLVMStoreInstruction) instruction;
                        if (store.getAddressValue() instanceof LLVMVariableLiteral
                            && store.getStoredValue() instanceof LLVMVariableLiteral
                            && this.isDebugUnsignedAlloca(funcName, ((LLVMVariableLiteral) store.getAddressValue()).getName())) {
                            res.add(new Pair<String,String>(funcName, ((LLVMVariableLiteral) store.getStoredValue()).getName()));
                        }
                    }
                }
            }
        }
    }

    /**
     * @param funcName The name of a function.
     * @param pointerName The name of a pointer (alloca) variable.
     * @return True iff the C source declared the variable living in the specified pointer (in the specified function) as
     *         an unsigned integer type (according to the debug metadata).
     */
    private boolean isDebugUnsignedAlloca(String funcName, String pointerName) {
        // Internal variable names carry their scope sigil ("%"/"@"), while the names recovered from the debug metadata
        // are stored without it. Normalize before comparing.
        String normalized = pointerName;
        if (normalized != null && !normalized.isEmpty()
            && (normalized.charAt(0) == '%' || normalized.charAt(0) == '@')) {
            normalized = normalized.substring(1);
        }
        return this.debugUnsignedAllocas.contains(new Pair<String,String>(funcName, normalized));
    }

    /**
     * @return The set of (function name, alloca variable name) pairs that hold an unsigned source variable according to
     *         the debug metadata.
     */
    public ImmutableSet<Pair<String,String>> getDebugUnsignedAllocas() {
        return this.debugUnsignedAllocas;
    }

    /**
     * @param pos The first program position.
     * @param succ The successor position.
     * @return YES, if pos is a conditional branch and other is the true-successor of pos.
     *         NO, if pos is a conditional branch and other is the false-successor of pos.
     *         MAYBE, if pos is not a conditional branch or other is no successor of pos.
     */
    public YNM controlResult(LLVMProgramPosition pos, LLVMProgramPosition other) {
        if (!(this.getInstruction(pos) instanceof LLVMCondBrInstruction)) return YNM.MAYBE;
        LLVMCondBrInstruction instrAtPos = (LLVMCondBrInstruction) this.getInstruction(pos);
        Node<LLVMProgramPosition> posNode = this.controlFlowGraph.getAllNodesFromObject(pos).iterator().next();
        for (Edge<String,LLVMProgramPosition> edge : this.controlFlowGraph.getOutEdges(posNode)) {
            LLVMProgramPosition succ = edge.getEndNode().getObject();
            if (succ.getBlock().equals(instrAtPos.getIfTrueLabel())) {
                return YNM.YES;
            }
            if (succ.getBlock().equals(instrAtPos.getIfFalseLabel())) {
                return YNM.NO;
            }
        }
        return YNM.MAYBE;
    }

    @Override
    public String export(Export_Util o) {
        StringBuilder res = new StringBuilder();
        res.append(o.export("Aliases:"));
        res.append(o.newline());
        res.append(o.set(this.aliasDefinitions.values(), Export_Util.ITEMIZE));
        res.append(o.export("Data layout:"));
        res.append(o.newline());
        res.append(o.export(this.dataLayout));
        res.append(o.newline());
        res.append(o.export("Machine:"));
        res.append(o.newline());
        res.append(o.export(this.getMachine()));
        res.append(o.newline());
        res.append(o.export("Type definitions:"));
        res.append(o.newline());
        StringBuilder indentation = new StringBuilder();
        for (Map.Entry<String, LLVMType> typeDef : this.typeDefinitions.entrySet()) {
            indentation.append(o.export(typeDef.getKey()));
            indentation.append(o.export(" --> "));
            indentation.append(o.export(typeDef.getValue()));
            indentation.append(o.newline());
        }
        res.append(o.indent(indentation.toString()));
        res.append(o.export("Global variables:"));
        res.append(o.newline());
        indentation = new StringBuilder();
        for (LLVMGlobalVariable variable : this.variables.values()) {
            indentation.append(o.export(variable));
            indentation.append(o.newline());
        }
        res.append(o.indent(indentation.toString()));
        res.append(o.export("Function declarations and definitions:"));
        res.append(o.newline());
        res.append(o.indent(o.set(this.fnDeclarations.values(), Export_Util.ITEMIZE)));
        return res.toString();
    }

   public String toLLVMIR() {
	    StringBuilder res = new StringBuilder();
        res.append(this.fnDeclarations.values().stream().map(x -> x.toLLVMIR()).collect(Collectors.joining("\n\n")));
        res.append("\n");
        return res.toString();
   }

    /**
     * @param type The type.
     * @return The ABI alignment for the specified type or 0 if no alignment is specified.
     */
    public int getAbiAlignment(LLVMType type) {
        if (type instanceof LLVMIntType) {
            switch (type.size()) {
            case 1: return Math.max(1, this.getI1Alignment() / 8);
            case 8: return Math.max(1, this.getI8Alignment() / 8);
            case 16: return Math.max(1, this.getI16Alignment() / 8);
            case 32: return Math.max(1, this.getI32Alignment() / 8);
            case 64: return Math.max(1, this.getI64Alignment() / 8);
            default:
                return 0;
            }
        } else if (type instanceof LLVMPointerType) {
            return Math.max(1, this.getPointerAlignment() / 8);
        }
        return 0;
    }

    /**
     * @return The set of addresses to unsigned variables.
     */
    public ImmutableSet<String> getAddressesToUnsignedBitvectorVariables() {
        LinkedHashSet<String> res = new LinkedHashSet<>();
        this.addressesToUnsignedBitvectorVariables.forEach(p -> res.add(p.getValue()));
        return ImmutableCreator.create(res);
    }

    /**
     * @return The alias definitions.
     */
    public ImmutableMap<String, LLVMAliasDefinition> getAliasDefs() {
        return this.aliasDefinitions;
    }

    /**
     * @return All program positions in this program.
     */
    public Set<LLVMProgramPosition> getAllPositions() {
        return LLVMModule.getAllPositions(this.getFunctions().values());
    }

    /**
     * @return A set of all program variable names occurring in this LLVM module.
     */
    public Set<String> getAllProgramVariableNames() {
        return
            LLVMModule.getAllProgramVariableNames(this.getVariableDefinitions().keySet(), this.getFunctions().values());
    }

    /**
     * @return The target data layout.
     * @see <a href="http://llvm.org/docs/LangRef.html#data-layout">The LLVM Documentation on Data Layouts</a>
     */
    public String getDataLayout() {
        return this.dataLayout;
    }

    public ImmutableMap<Integer, LLVMDebugInformation> getDebugInformation() {
        return this.debugInformation;
    }

    public LLVMDebugInformation getDebugInformation(int i) {
        return this.debugInformation.get(i);
    }

    /**
     * @return The function declarations/definitions.
     */
    public ImmutableMap<String, LLVMFnDeclaration> getFunctions() {
        return this.fnDeclarations;
    }

    /**
     * @return the alignment used for an i16
     */
    public int getI16Alignment() {
        return this.i16Alignment;
    }

    /**
     * @return the alignment used for an i1
     */
    public int getI1Alignment() {
        return this.i1Alignment;
    }

    /**
     * @return the alignment used for an i32
     */
    public int getI32Alignment() {
        return this.i32Alignment;
    }

    /**
     * @return the alignment used for an i64
     */
    public int getI64Alignment() {
        return this.i64Alignment;
    }

    /**
     * @return the alignment used for an i8
     */
    public int getI8Alignment() {
        return this.i8Alignment;
    }

    /**
     * @param pos The program position.
     * @return The instruction at the specified program position.
     */
    public LLVMInstruction getInstruction(LLVMProgramPosition pos) {
        return ((LLVMFnDefinition)this.fnDeclarations.get(pos.getFunction())).getBlocks().get(pos.getBlock()).getInstructions().get(pos.getLine());
    }

    public int getLineOfFirstNonPhiStatement(String fnName, String blockName) {
        List<LLVMInstruction> instructions = ((LLVMFnDefinition)this.fnDeclarations.get(fnName)).getBlocks().get(blockName).getInstructions();
        for (int i = 0; i < instructions.size(); i++) {
            if (instructions.get(i) instanceof LLVMPhiInstruction) {
                continue;
            }
            return i;
        }
        throw new IllegalStateException("Block " + blockName + " in function " + fnName + " doesn't contain a non-phi instruction");
    }

    /**
     * @return The mapping from program positions to live program variables.
     */
    public ImmutableMap<LLVMProgramPosition, ImmutableSet<String>> getLiveVariables() {
        return this.liveVariables;
    }

    /**
     * @return The target machine.
     */
    public String getMachine() {
        return this.machine;
    }

    /**
     * @return the pointer size
     */
    public int getPointerAlignment() {
        return this.pointerAlignment;
    }

    /**
     * @return the pointer size in bits
     */
    public int getPointerSize() {
        return this.pointerSize;
    }

    /**
     * @param useBoundedIntegers Use bounded integers?
     * @return The pointer type as integer type.
     */
    public IntegerType getPointerType(boolean useBoundedIntegers) {
        return LLVMPointerType.getIntegerType(this.pointerSize, useBoundedIntegers);
    }

    /**
     * @return the set of program specific literal relations
     */
    public ImmutableSet<LLVMLiteralRelation> getProgramLiteralRelations() {
        return this.programLiteralRelations;
    }

    /**
     * @return the set of program specific reference relations
     */
    public ImmutableSet<LLVMRelation> getProgramReferenceRelations() {
        return this.programReferenceRelations;
    }

    /**
     * @return The mapping from program positions to return conditions.
     */
    public ImmutableMap<LLVMProgramPosition, ImmutableSet<ImmutableSet<IntegerRelation>>> getReturnConditions() {
        return this.returnConditions;
    }

    /**
     * @return The type definitions.
     */
    public ImmutableMap<String, LLVMType> getTypeDefinitions() {
        return this.typeDefinitions;
    }

    /**
     * @return The set of unsigned variables.
     */
    public ImmutableSet<String> getUnsignedBitvectorVariables() {
        LinkedHashSet<String> res = new LinkedHashSet<>();
        this.unsignedBitvectorVariables.forEach(p -> res.add(p.getValue()));
        return ImmutableCreator.create(res);
    }

    /**
     * @return The set of unsigned variables.
     */
    public ImmutableSet<String> getUnsignedUnboundedVariables() {
        LinkedHashSet<String> res = new LinkedHashSet<>();
        this.unsignedUnboundedVariables.forEach(p -> res.add(p.getValue()));
        return ImmutableCreator.create(res);
    }

    /**
     * @return The set of unsigned variables.
     */
    public ImmutableSet<Pair<String,String>> getUnsignedUnboundedVariablesPair() {
        return this.unsignedUnboundedVariables;
    }

    /**
     * @return The global variables.
     */
    public ImmutableMap<String, LLVMGlobalVariable> getVariableDefinitions() {
        return this.variables;
    }

    /**
     * @param funcs The new functions.
     * @return This LLVM module where the functions have been set to the specified ones.
     */
    public LLVMModule setFunctions(Map<String, LLVMFnDeclaration> funcs) {
        return
            new LLVMModule(
                this.getAliasDefs(),
                this.getDataLayout(),
                this.getDebugInformation(),
                ImmutableCreator.create(funcs),
                this.getMachine(),
                this.getTypeDefinitions(),
                this.getVariableDefinitions(),
                this.getProgramReferenceRelations(),
                this.getLiveVariables(),
                this.getReturnConditions(),
                this.getDebugUnsignedAllocas(),
                this.getPointerSize()
            );
    }

    /**
     * @param liveVars The new live variables.
     * @return This LLVM module where the live variables have been set to the specified ones.
     */
    public LLVMModule setLiveVariables(Map<LLVMProgramPosition, ImmutableSet<String>> liveVars) {
        return
            new LLVMModule(
                this.getAliasDefs(),
                this.getDataLayout(),
                this.getDebugInformation(),
                this.getFunctions(),
                this.getMachine(),
                this.getTypeDefinitions(),
                this.getVariableDefinitions(),
                this.getProgramReferenceRelations(),
                ImmutableCreator.create(liveVars),
                this.getReturnConditions(),
                this.getDebugUnsignedAllocas(),
                this.getPointerSize()
            );
    }

    /**
     * @param retConds The new return conditions.
     * @return This LLVM module where the return conditions have been set to the specified ones.
     */
    public LLVMModule setReturnConditions(Map<LLVMProgramPosition, ImmutableSet<ImmutableSet<IntegerRelation>>> retConds) {
        return
            new LLVMModule(
                this.getAliasDefs(),
                this.getDataLayout(),
                this.getDebugInformation(),
                this.getFunctions(),
                this.getMachine(),
                this.getTypeDefinitions(),
                this.getVariableDefinitions(),
                this.getProgramReferenceRelations(),
                this.getLiveVariables(),
                ImmutableCreator.create(retConds),
                this.getDebugUnsignedAllocas(),
                this.getPointerSize()
            );
    }

    @Override
    public Object toJSON() {
        JSONObject res = new JSONObject();
        res.put("type", "LLVMModule");
        res.put("aliases", JSONExportUtil.toJSON(this.getAliasDefs()));
        res.put("data_layout", this.getDataLayout());
        res.put("functions", JSONExportUtil.toJSON(this.getFunctions()));
        res.put("live_variables", JSONExportUtil.toJSON(this.getLiveVariables()));
        res.put("machine", this.getMachine());
        res.put("return_conditions", JSONExportUtil.toJSON(this.getReturnConditions()));
        res.put("type_defs", JSONExportUtil.toJSON(this.getTypeDefinitions()));
        res.put("global_vars", JSONExportUtil.toJSON(this.getVariableDefinitions()));
        return res;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    /**
     * Returns the parameters of a given function with leading %
     * @param functionName (without leading @)
     * @return
     */
    public Set<String> getFunctionParameters(String functionName) {
    	LLVMFnDeclaration decl = getFunctions().get(functionName);
    	if(!(decl instanceof LLVMFnDefinition)) {
    		throw new IllegalArgumentException();
    	} else {
    		LLVMFnDefinition def = (LLVMFnDefinition) decl;
    		return def.getParameters()
    			.stream()
    			.map(p -> "%" + p.getName())
    			.collect(Collectors.toCollection(LinkedHashSet::new));
    	}
    }

    /**
     * Give a name to triples of program positions, instructions, and sets of relation sets.
     * @author cryingshadow
     * @version $Id$
     */
    private static class RetCond
    extends Triple<LLVMProgramPosition, LLVMInstruction, Set<Pair<IntegerRelationSet, List<String>>>> {

        /**
         * @param pos The program position.
         * @param instruction The instruction at pos.
         * @param conditions The return conditions at pos.
         */
        public RetCond(
            LLVMProgramPosition pos,
            LLVMInstruction instruction,
            Set<Pair<IntegerRelationSet, List<String>>> conditions
        ) {
            super(pos, instruction, conditions);
        }

    }

}
