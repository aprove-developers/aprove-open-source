package aprove.input.Programs.llvm.parseStructures;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.expressions.relations.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.dataTypes.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.input.Programs.llvm.parseStructures.literals.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * This class contains the parsed data of an LLVM program in a first crude representation. This class can be converted
 * to an LLVMModule which has more complex data structures (e.g., for instructions) and also some type resolving (type
 * definitions are resolved).
 * @author Janine Repke, cryingshadow
 */
public class LLVMParseModule {

    private final LinkedHashSet<LLVMParseAliasDefinition> aliasDefinitions = new LinkedHashSet<LLVMParseAliasDefinition>();

    /**
     * Contains the layout specification.
     */
    private String dataLayout;
    
    private final LinkedHashMap<LLVMParseLiteral, LLVMParseDebugInformation> debugInformation = new LinkedHashMap<>();

    private final LinkedHashSet<LLVMParseFunctionDeclaration> fnDeclarations = new LinkedHashSet<LLVMParseFunctionDeclaration>();

    private final LinkedHashSet<LLVMParseFunctionDefinition> functions = new LinkedHashSet<LLVMParseFunctionDefinition>();

    /**
     * Specifies the target machine.
     */
    private String machine;

    private final LinkedHashMap<String, LLVMParseType> typeDefinitions = new LinkedHashMap<String, LLVMParseType>();

    /**
     * Global variables.
     */
    private final LinkedHashSet<LLVMParseVariable> variables = new LinkedHashSet<LLVMParseVariable>();

    public void addAliasDefinition(final LLVMParseAliasDefinition aliasDefinition) {
        this.aliasDefinitions.add(aliasDefinition);
    }
    
    public void addDebugInformation(final LLVMParseDebugInformation debugInformation) {
        this.debugInformation.put(debugInformation.getIndex(), debugInformation);
    }

    public void addFunctionDeclaration(final LLVMParseFunctionDeclaration fnDeclaration) {
        this.fnDeclarations.add(fnDeclaration);
    }

    public void addFunctionDefinition(final LLVMParseFunctionDefinition fnDefinition) {
        this.functions.add(fnDefinition);
    }

    public void addGlobalVariable(final LLVMParseVariable var) {
        this.variables.add(var);
    }

    public void addTypeDefinition(final String typeName, final LLVMParseType type) {
        this.typeDefinitions.put(typeName, type);
    }

    public LLVMModule createBasicStructure() throws LLVMParseException {
        final int pointerSize = this.computePointerSizeFromDataLayout();
        // convert type definitions
        final Map<String, LLVMType> typeDefs = new LinkedHashMap<String, LLVMType>();
        int iterations = 5;
        while (iterations > 0) {
            iterations--;
            for (final Map.Entry<String, LLVMParseType> entry : this.typeDefinitions.entrySet()) {
                LLVMType basicType = null;
                if (entry.getValue() != null) {
                    basicType = entry.getValue().convertToBasicType(typeDefs, pointerSize);
                }
                typeDefs.put(entry.getKey(), basicType);
            }
        }
        // for nested types, we might do this again
        for (final Map.Entry<String, LLVMParseType> entry : this.typeDefinitions.entrySet()) {
            LLVMType basicType = null;
            if (entry.getValue() != null) {
                basicType = entry.getValue().convertToBasicType(typeDefs, pointerSize);
            }
            typeDefs.put(entry.getKey(), basicType);
        }
        // convert alias definitions
        final Map<String, LLVMAliasDefinition> aliases = new LinkedHashMap<String, LLVMAliasDefinition>();
        for (final LLVMParseAliasDefinition aliasDef : this.aliasDefinitions) {
            final LLVMAliasDefinition alias = aliasDef.convertToAliasDefinition(typeDefs, pointerSize);
            aliases.put(alias.getAlias(), alias);
        }
        // convert debug information
        final Map<Integer, LLVMDebugInformation> debugInfo = new LinkedHashMap<>();
        for (final Map.Entry<LLVMParseLiteral, LLVMParseDebugInformation> dInfo : this.debugInformation.entrySet()) {
            final LLVMDebugInformation info = dInfo.getValue().convertToDebugInformation(pointerSize);
            debugInfo.put(info.getIndex(), info);
        }
        // convert function declarations
        final Map<String, LLVMFnDeclaration> funcDecls = new LinkedHashMap<String, LLVMFnDeclaration>();
        for (final LLVMParseFunctionDeclaration fnDeclaration : this.fnDeclarations) {
            final LLVMFnDeclaration funcDecl = fnDeclaration.convertToFnDeclaration(typeDefs, pointerSize);
            funcDecls.put(funcDecl.getName(), funcDecl);
        }
        // convert function definitions (contains blocks and the blocks contain instructions)
        for (final LLVMParseFunctionDefinition function : this.functions) {
            final LLVMFnDefinition funcDef = function.convertToFnDefinition(typeDefs, pointerSize);
            funcDecls.put(funcDef.getName(), funcDef);
        }
        // convert global variable definitions
        final Map<String, LLVMGlobalVariable> globalVarDefs = new LinkedHashMap<String, LLVMGlobalVariable>();
        for (final LLVMParseVariable variable : this.variables) {
            final LLVMGlobalVariable globalVariable = variable.convertToGlobalVariable(typeDefs, pointerSize);
            globalVarDefs.put(globalVariable.getName(), globalVariable);
        }
        return
            new LLVMModule(
                ImmutableCreator.create(aliases),
                this.dataLayout,
                ImmutableCreator.create(debugInfo),
                ImmutableCreator.create(funcDecls),
                this.machine,
                ImmutableCreator.create(typeDefs),
                ImmutableCreator.create(globalVarDefs),
                ImmutableCreator.create(new LinkedHashSet<LLVMRelation>()),
                null,
                null,
                this.computeDebugUnsignedAllocas(pointerSize),
                pointerSize
            );
    }

    /**
     * Recovers, from the debug metadata, the set of (function name, alloca variable name) pairs for which the C source
     * declared the variable living in the alloca as an unsigned integer type. The chain is:
     * llvm.dbg.declare binds an alloca pointer to a DILocalVariable, whose type (possibly via DIDerivedType wrappers
     * such as typedef/const) is a DIBasicType with an encoding (DW_ATE_unsigned).
     * @param pointerSize The pointer size (needed to read the numeric metadata indices).
     * @return The set of unsigned allocas, keyed by (function name, alloca variable name).
     */
    private ImmutableSet<Pair<String,String>> computeDebugUnsignedAllocas(final int pointerSize) {
        final LinkedHashSet<Pair<String,String>> res = new LinkedHashSet<Pair<String,String>>();
        // index the debug metadata nodes by their numeric index (e.g. the 12 in "!12 = !DIBasicType(...)")
        final Map<Integer, LLVMParseDebugInformation> diByIndex = new LinkedHashMap<Integer, LLVMParseDebugInformation>();
        for (final Map.Entry<LLVMParseLiteral, LLVMParseDebugInformation> e : this.debugInformation.entrySet()) {
            try {
                diByIndex.put(e.getKey().convertToI32(pointerSize), e.getValue());
            } catch (final LLVMParseException ex) {
                // ignore metadata nodes whose index is not a plain integer
            }
        }
        for (final LLVMParseFunctionDefinition function : this.functions) {
            final String funcName = function.getName();
            for (final LLVMParseBlock block : function.getBlocks()) {
                for (final LLVMParseInstruction instr : block.getInstructions()) {
                    final LLVMParseLiteral ptr = instr.getDbgDeclarePointer();
                    if (ptr instanceof LLVMParseVariableLiteral
                        && instr.getDbgDeclareLocalVarIndex() >= 0
                        && LLVMParseModule.isUnsignedLocalVariable(instr.getDbgDeclareLocalVarIndex(), diByIndex)) {
                        res.add(new Pair<String,String>(funcName, ((LLVMParseVariableLiteral)ptr).getName()));
                    }
                }
            }
        }
        return ImmutableCreator.create(res);
    }

    /**
     * @param localVarIndex The index of a DILocalVariable debug metadata node.
     * @param diByIndex All debug metadata nodes indexed by their numeric index.
     * @return True iff the type of the specified DILocalVariable is an unsigned integer type.
     */
    private static boolean isUnsignedLocalVariable(
        final int localVarIndex,
        final Map<Integer, LLVMParseDebugInformation> diByIndex
    ) {
        final LLVMParseDebugInformation localVar = diByIndex.get(localVarIndex);
        if (localVar == null) {
            return false;
        }
        return LLVMParseModule.isUnsignedType(LLVMParseModule.parseMetadataRef(localVar.getField("type")), diByIndex, 0);
    }

    /**
     * @param typeIndex The index of a type debug metadata node.
     * @param diByIndex All debug metadata nodes indexed by their numeric index.
     * @param depth The current recursion depth (to guard against cyclic metadata).
     * @return True iff the specified type (chasing DIDerivedType wrappers) is a DIBasicType with an unsigned encoding.
     */
    private static boolean isUnsignedType(
        final int typeIndex,
        final Map<Integer, LLVMParseDebugInformation> diByIndex,
        final int depth
    ) {
        if (typeIndex < 0 || depth > 32) {
            return false;
        }
        final LLVMParseDebugInformation node = diByIndex.get(typeIndex);
        if (node == null) {
            return false;
        }
        if ("DIBasicType".equals(node.getKind())) {
            final String encoding = node.getField("encoding");
            return "DW_ATE_unsigned".equals(encoding)
                || "DW_ATE_unsigned_char".equals(encoding)
                || "DW_ATE_boolean".equals(encoding);
        }
        // for wrappers like DIDerivedType (typedef, const, volatile, ...), follow the base type
        return LLVMParseModule.isUnsignedType(
            LLVMParseModule.parseMetadataRef(node.getField("baseType")),
            diByIndex,
            depth + 1
        );
    }

    /**
     * @param value The text of a metadata field value (e.g. "!12").
     * @return The numeric metadata index (e.g. 12), or -1 if the value is not a metadata reference.
     */
    private static int parseMetadataRef(final String value) {
        if (value == null) {
            return -1;
        }
        String v = value.trim();
        if (v.startsWith("!")) {
            v = v.substring(1).trim();
        }
        try {
            return Integer.parseInt(v);
        } catch (final NumberFormatException e) {
            return -1;
        }
    }

    public void debugOutput() {
        if (this.variables != null) {
            final Iterator<LLVMParseVariable> it = this.variables.iterator();
            while (it.hasNext()) {
                final LLVMParseVariable var = it.next();
                System.err.println(var.toString());
            }
        }
    }

    public String getDataLayout() {
        return this.dataLayout;
    }

    public String getTriple() {
        return this.machine;
    }

    public LLVMParseType getTypeDefinition(final String typeName) {
        return (this.typeDefinitions.get(typeName));
    }

    public void setDataLayout(final String dataLayout) {
        this.dataLayout = dataLayout;
    }

    public void setTriple(final String triple) {
        this.machine = triple;
    }

    @Override
    public String toString() {
        StringBuilder res = new StringBuilder();
        res.append(this.machine);
        res.append("\n");
        res.append(this.dataLayout);
        res.append("\n");
        res.append(this.typeDefinitions);
        res.append("\n");
        res.append(this.variables);
        res.append("\n");
        res.append(this.fnDeclarations);
        res.append("\n");
        res.append(this.functions);
        res.append("\n");
        res.append(this.aliasDefinitions);
        return res.toString();
    }

    /**
     * @param dataLayout The dataLayout that specifies the pointer type.
     * @return The size of a pointer used throughout the module.
     */
    private int computePointerSizeFromDataLayout() {
        // the relevant part of the layout string is of the form "p:size:"
        int indexStart = this.dataLayout.indexOf("p:") + 2;
        int indexEnd = this.dataLayout.indexOf(':', indexStart);
        if (indexStart > 1) {
            if (this.dataLayout.substring(indexStart, indexStart + 1).equals("m")) {
                // We have an M1 processor. The size starts after the "m".
                indexStart++;
            }
            String pointerSize = this.dataLayout.substring(indexStart, indexEnd);
            return Integer.parseInt(pointerSize);
        } else {
            indexStart = this.machine.indexOf("x86_") + 4;
            indexEnd = this.machine.indexOf('-', indexStart);
            if (this.machine.substring(indexStart, indexStart + 1).equals("m")) {
                // We have an M1 processor. The size starts after the "m".
                indexStart++;
            }
            String pointerSize = this.machine.substring(indexStart, indexEnd);
            return Integer.parseInt(pointerSize);
        }
    }

}
