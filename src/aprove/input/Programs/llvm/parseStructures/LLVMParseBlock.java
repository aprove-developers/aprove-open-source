package aprove.input.Programs.llvm.parseStructures;

import java.util.*;

import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import immutables.*;

/**
 * A parse block is a list of instructions with an optional name. A function
 * definition contains parse blocks.
 */
public class LLVMParseBlock {

    private String blockName = null; // TODO label name is optional

    private ArrayList<LLVMParseInstruction> instructions = new ArrayList<LLVMParseInstruction>();

    public LLVMParseBlock(String labelName) {
        this.blockName = labelName;
    }

    public void addInstruction(LLVMParseInstruction instruction) {
        this.instructions.add(instruction);
    }

    public LLVMBasicBlock convertToBasicBlock(Map<String, LLVMType> typeDefs, int pointerSize) throws LLVMParseException {
        // convert instructions
        final List<LLVMInstruction> instrList = new ArrayList<LLVMInstruction>();
        for (LLVMParseInstruction instruction : this.instructions) {
            // debug intrinsics (llvm.dbg.*) are not analyzed - their information is extracted separately
            if (instruction.isDbgIntrinsic()) {
                continue;
            }
            instrList.add(instruction.convertToBasicInstruction(typeDefs, pointerSize));
        }
        return new LLVMBasicBlock(this.blockName, ImmutableCreator.create(instrList));
    }

    public ArrayList<LLVMParseInstruction> getInstructions() {
        return this.instructions;
    }

    public String getLabelName() {
        return this.blockName;
    }

    public void setInstructions(ArrayList<LLVMParseInstruction> instructions) {
        this.instructions = instructions;
    }

    @Override
    public String toString() {
        return this.blockName + ": " + this.instructions.toString();
    }

}
