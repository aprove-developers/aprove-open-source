package aprove.input.Programs.llvm.parseStructures;

import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.input.Programs.llvm.parseStructures.literals.*;
import immutables.*;

public class LLVMParseFunctionDefinition extends LLVMParseFunctionDeclaration {

    private final ArrayList<LLVMParseBlock> blocks = new ArrayList<LLVMParseBlock>();
    protected LLVMParseLiteral debugLine = null;
    private LLVMParseLiteral section; // TODO: also possible for function declarations?

    public void addBlock(LLVMParseBlock block) {
        this.blocks.add(block);
    }

    public ArrayList<LLVMParseBlock> getBlocks() {
        return this.blocks;
    }

    public LLVMFnDefinition convertToFnDefinition(Map<String, LLVMType> typeDefs, int pointerSize)
    throws LLVMParseException {
        // convert instruction blocks
        String firstBlock = null;
        boolean first = true;
        final Map<String, LLVMBasicBlock> basicBlocks = new LinkedHashMap<String, LLVMBasicBlock>();
        for (LLVMParseBlock block : this.blocks) {
            if (first) {
                firstBlock = block.getLabelName();
                first = false;
            }
            basicBlocks.put(block.getLabelName(), block.convertToBasicBlock(typeDefs, pointerSize));
        }
        if (Globals.useAssertions) {
            assert (firstBlock != null) : "Did not find any first block!";
        }
        return
            new LLVMFnDefinition(
                this.alignment == null ? null : this.alignment.convertToAlignment(pointerSize),
                ImmutableCreator.create(this.attributes),
                this.callConv,
                this.debugLine == null ? -1 : this.debugLine.convertToI32(pointerSize),
                this.garColl,
                this.linkageType,
                this.name,
                this.convertToFnParameters(typeDefs, pointerSize),
                this.returnParam.convertToFnParameter(typeDefs, pointerSize),
                this.variableLength,
                this.visType,
                this.section == null ? null : this.section.convertToSection(),
                firstBlock,
                ImmutableCreator.create(basicBlocks)
            );
    }

    public LLVMParseLiteral getSection() {
        return this.section;
    }
    
    public void setDebugLine(LLVMParseLiteral debugLine) {
        this.debugLine = debugLine;
    }

    public void setSection(LLVMParseLiteral section) {
        this.section = section;
    }

    @Override
    public String toString() {
        return super.toString() + "\n" + this.blocks.toString();
    }

}
