package aprove.input.Programs.llvm.parseStructures;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.input.Programs.llvm.parseStructures.literals.*;

public class LLVMParseDebugInformation {

    private LLVMParseLiteral index;

    private String functionName;

    private LLVMParseLiteral cLine;

    /**
     * The kind of a generic debug metadata node (e.g. "DIBasicType", "DILocalVariable", "DIDerivedType"). May be
     * <code>null</code> for nodes parsed by the dedicated DISubprogram/DILocation branches.
     */
    private String kind;

    /**
     * The fields of a generic debug metadata node mapped from key to value text (e.g. "encoding" -> "DW_ATE_unsigned",
     * "type" -> "!12"). Used to recover the source-level signedness of variables.
     */
    private final Map<String, String> fields = new LinkedHashMap<String, String>();

    public LLVMDebugInformation convertToDebugInformation(int pointerSize)
    throws LLVMParseException {
        return
            new LLVMDebugInformation(
                this.index.convertToI32(pointerSize),
                this.functionName,
                this.cLine == null? -1 : this.cLine.convertToI32(pointerSize)
            );
    }
    
    public LLVMParseLiteral getcLine() {
        return this.cLine;
    }
    
    public String getFunctionName() {
        return this.functionName;
    }
    
    public LLVMParseLiteral getIndex() {
        return this.index;
    }

    public String getKind() {
        return this.kind;
    }

    public void setKind(String kind) {
        this.kind = kind;
    }

    public void addField(String key, String value) {
        this.fields.put(key, value);
    }

    public String getField(String key) {
        return this.fields.get(key);
    }

    public void setCLine(LLVMParseLiteral line) {
        this.cLine = line;
    }
    
    public void setFunctionName(String fname) {
        this.functionName = fname;
    }
    
    public void setIndex(LLVMParseLiteral index) {
        this.index = index;
    }
    
}
