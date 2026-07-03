package aprove.input.Programs.llvm.parseStructures;

import java.util.*;

import aprove.*;
import aprove.input.Programs.llvm.internalStructures.dataType.*;
import aprove.input.Programs.llvm.internalStructures.instructions.*;
import aprove.input.Programs.llvm.internalStructures.literals.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
import aprove.input.Programs.llvm.parseStructures.dataTypes.*;
import aprove.input.Programs.llvm.parseStructures.exceptions.*;
import aprove.input.Programs.llvm.parseStructures.literals.*;
import immutables.*;

/**
 * @author Janine Repke, cryingshadow
 * Instruction raw type.
 * TODO build in more checks w.r.t. the types!
 */
public class LLVMParseInstruction {

    /**
     * Checks if the binary operation is of type udiv, sdiv, lshr or ashr. Only these operation types can be
     * used with the exact specifier. This function is used in the parser instead of directly checking this
     * property with the parse grammar, which would make the grammar more complex and more complicated to read.
     * @param binaryOpType The operation to check.
     * @return True if the operation is compatible with the exact specifier. False otherwise.
     */
    public static boolean isBinaryOpExactCompatible(LLVMBinaryOpType binaryOpType) {
        switch (binaryOpType) {
            case ASHR:
            case LSHR:
            case SDIV:
            case UDIV:
                // these binary op types can be used with the exact speicifer
                return true;
            default:
                return false;
        }
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs
     * @param pointerSize The pointer size.
     * @return The converted AllocaInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToAllocaInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // identifier (needs pointerType to be converted, so do this later)
        LLVMParseLiteral id = (LLVMParseLiteral)objIt.next();
        // type of the pointer to the allocated memory
        LLVMType pointerType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // number of elements
        LLVMLiteral numberOfElements = null;
        if ((Boolean)objIt.next()) {
            LLVMType bType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
            if (Globals.useAssertions) {
                assert (bType.isIntType()) : "Number is no number!";
            }
            numberOfElements = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(bType, true, typeDefs, pointerSize);
        }
        // alignment
        LLVMLiteral align = null;
        if ((Boolean)objIt.next()) {
            align = ((LLVMParseLiteral)objIt.next()).convertToAlignment(pointerSize);
        }
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return new LLVMAllocaInstruction(id.convertToIdentifier(pointerType), pointerType, numberOfElements, align, debugLine);
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted BinaryInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToBinaryInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // identifier (needs opType to be converted, so do this later)
        LLVMParseLiteral id = (LLVMParseLiteral)objIt.next();
        // binary operator
        LLVMBinaryOpType operator = (LLVMBinaryOpType)objIt.next();
        // exact
        boolean exact = (Boolean)objIt.next();
        // nuw
        boolean nuw = (Boolean)objIt.next();
        // nsw
        boolean nsw = (Boolean)objIt.next();
        // operand type
        LLVMType opType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // first operand value
        LLVMLiteral op1 = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(opType, false, typeDefs, pointerSize);
        // second operand value
        LLVMLiteral op2 = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(opType, false, typeDefs, pointerSize);
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return new LLVMBinaryInstruction(id.convertToIdentifier(opType), op1, op2, operator, exact, nsw, nuw, debugLine);
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted CallInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToCallInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        /*
         * The following construction with the stored identifier and the setIdentifier flag is needed, because we need
         * to get the objects from the iterator in the right order and we need the type of a later object to process
         * the identifier.
         */
        LLVMParseLiteral storeIdentifier = null;
        boolean setIdentifier = false;
        if ((Boolean)objIt.next()) {
            // identifier is given
            storeIdentifier = (LLVMParseLiteral)objIt.next();
            setIdentifier = true;
        }
        boolean tail = (Boolean)objIt.next();
        // calling convention
        LLVMCallingConvention callingConvention = null;
        if ((Boolean)objIt.next()) {
            callingConvention = (LLVMCallingConvention)objIt.next();
        }
        int numRetParams = (Integer)objIt.next();
        List<LLVMParameterAttribute> retAttrs = new ArrayList<LLVMParameterAttribute>();
        for (int i = 0; i < numRetParams; i++) {
            retAttrs.add((LLVMParameterAttribute)objIt.next());
        }
        // return type
        LLVMType returnType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // signature
        List<LLVMType> signature = null;
        boolean moreTypes = false;
        if ((Boolean)objIt.next()) {
            signature = new ArrayList<LLVMType>();
            int numSigTypes = (Integer)objIt.next();
            for (int i = 0; i < numSigTypes - 1; i++) {
                signature.add(((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize));
            }
            LLVMParseType lastType = (LLVMParseType)objIt.next();
            if (lastType == null) {
                moreTypes = true;
            } else {
                signature.add(lastType.convertToBasicType(typeDefs, pointerSize));
            }
        }
        // function name
        LLVMParseLiteral funcName = (LLVMParseLiteral)objIt.next();
        // function parameters
        // number of parameters (should be an even number)
        int paramNumber = (Integer)objIt.next();
        if (Globals.useAssertions) {
            assert (paramNumber % 2 == 0) : "Number of parameters is not even!";
        }
        List<ImmutablePair<LLVMFnParameter, LLVMLiteral>> params =
            new ArrayList<ImmutablePair<LLVMFnParameter, LLVMLiteral>>();
        for (int i = 0; i < paramNumber / 2; i++) {
            // next parameter
            LLVMFnParameter nextFnParam = ((LLVMParseFunctionParameter)objIt.next()).convertToFnParameter(typeDefs, pointerSize);
            params.add(
                new ImmutablePair<LLVMFnParameter, LLVMLiteral>(
                    nextFnParam,
                    ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(nextFnParam.getType(), false, typeDefs, pointerSize)
                )
            );
        }
        // function attributes
        // number of attributes
        int attrNumber = (Integer)objIt.next();
        List<LLVMFunctionAttribute> attrs = new ArrayList<LLVMFunctionAttribute>();
        for (int i = 0; i < attrNumber; i++) {
            // next attribute
            attrs.add((LLVMFunctionAttribute)objIt.next());
        }
        // debug line
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return
            new LLVMCallInstruction(
                (setIdentifier ? storeIdentifier.convertToIdentifier(returnType) : null),
                callingConvention,
                ImmutableCreator.create(attrs),
                ImmutableCreator.create(retAttrs),
                funcName.convertToIdentifier(returnType),
                signature == null ? null : ImmutableCreator.create(signature),
                moreTypes,
                ImmutableCreator.create(params),
                tail,
                debugLine
            );
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted CondBrInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToCondBrInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // condition type (always i1, ignored):
        LLVMType conditionType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (conditionType.isBooleanType()) : "Condition is not i1!";
        }
        // condition literal
        LLVMLiteral conditionLiteral =
            ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(LLVMIntType.I1, true, typeDefs, pointerSize);
        // if true type (always label, ignored):
        LLVMType ifTrueType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (ifTrueType.isLabelType()) : "Label is no label!";
        }
        // ifTrue label
        String ifTrueTargetLabel = ((LLVMParseLiteral)objIt.next()).convertToLabelName();
        // if false type (always label, ignored):
        LLVMType ifFalseType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (ifFalseType.isLabelType()) : "Label is no label!";
        }
        // ifFalse label
        String ifFalseTargetLabel = ((LLVMParseLiteral)objIt.next()).convertToLabelName();
        // debug line
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return new LLVMCondBrInstruction(conditionLiteral, ifTrueTargetLabel, ifFalseTargetLabel, debugLine);
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted ConversionInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToConversionInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // identifier of the target variable (needs toType to be converted, so do this later)
        LLVMParseLiteral targetLiteral = (LLVMParseLiteral)objIt.next();
        // conversion type
        LLVMConvInstrType convType = (LLVMConvInstrType)objIt.next();
        // from type
        LLVMType fromType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // from value
        LLVMLiteral fromValue = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(fromType, false, typeDefs, pointerSize);
        // to type
        LLVMType toType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // debug line
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return new LLVMConversionInstruction(targetLiteral.convertToIdentifier(toType), fromValue, convType, debugLine);
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted ExtractElementInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToExtractElementInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // identifier (needs vecType to be converted, so do this later)
        LLVMParseLiteral id = (LLVMParseLiteral)objIt.next();
        // vector type
        LLVMType vecType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // TODO check whether we need to remove the vector type
        // vector literal
        LLVMLiteral vector = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(vecType, false, typeDefs, pointerSize);
        // index type - should be i32
        LLVMType indexType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (indexType.isIntTypeOfSize(32)) : "Index is no i32!";
        }
        // index literal
        LLVMLiteral index = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(indexType, false, typeDefs, pointerSize);
        // debug line
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return new LLVMExtractElementInstruction(id.convertToIdentifier(vecType), index, vector, debugLine);
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted ExtractValueInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToExtractValueInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // identifier (needs return type to be converted, so do this later)
        LLVMParseLiteral id = (LLVMParseLiteral)objIt.next();
        // aggregate type
        LLVMType aggregateType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // aggregate literal
        LLVMLiteral aggregate = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(aggregateType, false, typeDefs, pointerSize);
        // index values
        int numberOfIndices = (Integer)objIt.next();
        List<LLVMLiteral> indices = new ArrayList<LLVMLiteral>();
        for (int i = 0; i < numberOfIndices; i++) {
            // next index
            // type of indices is not specified in the code or the language reference manual
            // we assume i32 TODO check this
            indices.add(((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(LLVMIntType.I32, false, typeDefs, pointerSize));
        }
        // debug line
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        try {
            return
                new LLVMExtractValueInstruction(
                    id.convertToIdentifier(aggregateType.getSubtype(indices)),
                    aggregate,
                    ImmutableCreator.create(indices),
                    debugLine
                );
        } catch (IllegalArgumentException e) {
            throw new LLVMParseException(e.getMessage());
        }
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted FloatCmpInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToFloatCmpInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // identifier (is always of type i1)
        LLVMVariableLiteral id = ((LLVMParseLiteral)objIt.next()).convertToIdentifier(LLVMIntType.I1);
        // comparison type
        LLVMFloatCmpOpType cmpType = (LLVMFloatCmpOpType)objIt.next();
        // operand type
        LLVMType opType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // first operand value
        LLVMLiteral op1 = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(opType, false, typeDefs, pointerSize);
        // second operand value
        LLVMLiteral op2 = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(opType, false, typeDefs, pointerSize);
        // debug line
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return new LLVMFCmpInstruction(id, cmpType, op1, op2, debugLine);
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted GetElementPtrInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToGetElementPtrInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // identifier (needs return type to be converted, so do this later)
        LLVMParseLiteral id = (LLVMParseLiteral)objIt.next();
        // inbounds?
        boolean inbounds = (Boolean)objIt.next();
        // pointer type
        LLVMType pointerType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // pointer literal
        LLVMLiteral pointer = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(pointerType, true, typeDefs, pointerSize);
        // indices
        // numberOfIndices must be an even number
        int numberOfIndices = (Integer)objIt.next();
        if (Globals.useAssertions) {
            assert (numberOfIndices % 2 == 0) : "Number of index objects is not even!";
        }
        List<LLVMLiteral> indices = new ArrayList<LLVMLiteral>();
        for (int i = 0; i < numberOfIndices / 2; i++) {
            // index type
            LLVMType indexType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
            // index literal
            indices.add(((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(indexType, false, typeDefs, pointerSize));
        }
        // debug line
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        // the first index does not refer to a subtype in GEP
        try {
            return
                new LLVMGetElementPtrInstruction(
                    id.convertToIdentifier(
                        new LLVMPointerType(
                            pointerType.getThisAsPointerType().getTargetType().getSubtype(
                                indices.subList(1, indices.size())
                            ),
                            pointerType.size(),
                            null
                        )
                    ),
                    pointer,
                    inbounds,
                    ImmutableCreator.create(indices),
                    debugLine
                );
        } catch (IllegalArgumentException e) {
            throw new LLVMParseException(e.getMessage());
        }
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted IndirectBrInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToIndirectBrInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // address type
        LLVMType addrType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // address literal
        LLVMLiteral address = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(addrType, true, typeDefs, pointerSize);
        // read possible labels
        // number of label objects must be even
        int numOfLabelObjs = (Integer)objIt.next();
        if (Globals.useAssertions) {
            assert (numOfLabelObjs % 2 == 0) : "Number of label objects is not even!";
        }
        List<String> labels = new ArrayList<String>();
        for (int i = 0; i < numOfLabelObjs / 2; i++) {
            // type is label and is not needed anymore
            LLVMType type = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
            if (Globals.useAssertions) {
                assert (type.isLabelType()) : "Label is no label!";
            }
            // literal
            labels.add(((LLVMParseLiteral)objIt.next()).convertToLabelName());
        }
        // debug line
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return new LLVMIndirectBrInstruction(address, ImmutableCreator.create(labels), debugLine);
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted InsertElementInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToInsertElementInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // identifier (needs vecType to be converted, so do this later)
        LLVMParseLiteral id = (LLVMParseLiteral)objIt.next();
        // vector type
        LLVMType vecType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // vector literal
        LLVMLiteral vector = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(vecType, false, typeDefs, pointerSize);
        // element type
        LLVMType elemType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // element literal
        LLVMLiteral element = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(elemType, false, typeDefs, pointerSize);
        // index type - should be i32
        LLVMType indexType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (indexType.isIntTypeOfSize(32)) : "Index is no i32!";
        }
        // index literal
        LLVMLiteral index = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(indexType, false, typeDefs, pointerSize);
        // debug line
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return new LLVMInsertElementInstruction(id.convertToIdentifier(vecType), element, index, vector, debugLine);
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted InsertValueInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToInsertValueInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // identifier (needs aggrType to be converted, so do this later)
        LLVMParseLiteral id = (LLVMParseLiteral)objIt.next();
        // aggregate type
        LLVMType aggrType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // aggregate literal
        LLVMLiteral aggregate = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(aggrType, false, typeDefs, pointerSize);
        // element type
        LLVMType elemType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // element literal
        LLVMLiteral element = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(elemType, false, typeDefs, pointerSize);
        // indices
        int numOfIndices = (Integer)objIt.next();
        List<LLVMLiteral> indices = new ArrayList<LLVMLiteral>();
        for (int k = 0; k < numOfIndices; k++) {
            // index literal (index type should be i32 - not documented in the manual)
            indices.add(((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(LLVMIntType.I32, false, typeDefs, pointerSize));
        }
        // debug line
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return
            new LLVMInsertValueInstruction(
                id.convertToIdentifier(aggrType),
                element,
                ImmutableCreator.create(indices),
                aggregate,
                debugLine
            );
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted IntCmpInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToIntCmpInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // identifier (has always type i1)
        LLVMVariableLiteral id = ((LLVMParseLiteral)objIt.next()).convertToIdentifier(LLVMIntType.I1);
        // comparison type
        LLVMIntCmpOpType compCode = (LLVMIntCmpOpType)objIt.next();
        // operand type
        LLVMType opType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // first operand value
        LLVMLiteral op1 = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(opType, false, typeDefs, pointerSize);
        // second operand value
        LLVMLiteral op2 = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(opType, false, typeDefs, pointerSize);
        // debug line
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return new LLVMICmpInstruction(id, compCode, op1, op2, debugLine);
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted InvokeInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToInvokeInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        /*
         * The following construction with the stored identifier and the setIdentifier flag is needed, because we need
         * to get the objects from the iterator in the right order and we need the type of a later object to process
         * the identifier.
         */
        LLVMParseLiteral storeIdentifier = null;
        boolean setIdentifier = false;
        if ((Boolean)objIt.next()) {
            // identifier is given
            storeIdentifier = (LLVMParseLiteral)objIt.next();
            setIdentifier = true;
        }
        // calling convention
        LLVMCallingConvention callConv = null;
        if ((Boolean)objIt.next()) {
            callConv = (LLVMCallingConvention)objIt.next();
        }
        // return param
        LLVMFnParameter returnParam = ((LLVMParseFunctionParameter)objIt.next()).convertToFnParameter(typeDefs, pointerSize);
        // function name
        LLVMVariableLiteral funcName = ((LLVMParseLiteral)objIt.next()).convertToIdentifier(returnParam.getType());
        // function parameters
        // number of parameter objects (should be an even number)
        int numOfParams = (Integer)objIt.next();
        if (Globals.useAssertions) {
            assert (numOfParams % 2 == 0) : "Number of parameter objects is not even!";
        }
        List<ImmutablePair<LLVMFnParameter, LLVMLiteral>> params =
            new ArrayList<ImmutablePair<LLVMFnParameter, LLVMLiteral>>();
        for (int i = 0; i < numOfParams / 2; i++) {
            // next parameter
            LLVMFnParameter fnParam = ((LLVMParseFunctionParameter)objIt.next()).convertToFnParameter(typeDefs, pointerSize);
            params.add(
                new ImmutablePair<LLVMFnParameter, LLVMLiteral>(
                    fnParam,
                    ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(fnParam.getType(), false, typeDefs, pointerSize)
                )
            );
        }
        // function attributes
        // number of attribute objects
        int numOfAttrs = (Integer)objIt.next();
        List<LLVMFunctionAttribute> attrs = new ArrayList<LLVMFunctionAttribute>();
        for (int i = 0; i < numOfAttrs; i++) {
            // next attribute
            attrs.add((LLVMFunctionAttribute)objIt.next());
        }
        // normal label
        String normal = ((LLVMParseLiteral)objIt.next()).convertToLabelName();
        // exception label
        String exception = ((LLVMParseLiteral)objIt.next()).convertToLabelName();
        // debug line
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return
            new LLVMInvokeInstruction(
                (setIdentifier ? storeIdentifier.convertToIdentifier(returnParam.getType()) : null),
                callConv,
                ImmutableCreator.create(attrs),
                returnParam,
                funcName,
                ImmutableCreator.create(params),
                normal,
                exception,
                debugLine
            );
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted LoadInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToLoadInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // identifier (needs the type the pointer is pointing to for conversion, so do this later):
        LLVMParseLiteral id = (LLVMParseLiteral)objIt.next();
        // volatile bit (ignored)
        objIt.next();
        // pointer type
        LLVMType pointerType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (pointerType.isPointerType()) : "Pointer is no pointer!";
        }
        // pointer literal
        LLVMLiteral pointer = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(pointerType, true, typeDefs, pointerSize);
        // alignment
        LLVMLiteral alignment = null;
        if ((Boolean)objIt.next()) {
            alignment = ((LLVMParseLiteral)objIt.next()).convertToAlignment(pointerSize);
        }
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return
            new LLVMLoadInstruction(
                id.convertToIdentifier(pointerType.getThisAsPointerType().getTargetType()),
                pointer,
                alignment,
                debugLine
            );
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted PhiInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToPhiInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // identifier (needs valType to be converted, so do this later)
        LLVMParseLiteral id = (LLVMParseLiteral)objIt.next();
        // value type
        LLVMType valType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // argument pairs
        // number of argument objects must be even
        int numOfArgs = (Integer)objIt.next();
        if (Globals.useAssertions) {
            assert (numOfArgs % 2 == 0) : "Number of argument objects is not even!";
        }
        List<ImmutablePair<String, LLVMLiteral>> args = new ArrayList<ImmutablePair<String, LLVMLiteral>>();
        for (int i = 0; i < numOfArgs / 2; i++) {
            // the literal to assign
            LLVMLiteral argument = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(valType, false, typeDefs, pointerSize);
            // the label to come from
            String label = ((LLVMParseLiteral)objIt.next()).convertToLabelName();
            args.add(new ImmutablePair<String, LLVMLiteral>(label, argument));
        }
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return new LLVMPhiInstruction(id.convertToIdentifier(valType), ImmutableCreator.create(args), debugLine);
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted ReturnInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToReturnInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        LLVMLiteral value = null;
        // void return?
        if ((Boolean)objIt.next()) {
            // return type is not void
            LLVMType retType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
            // return value
            value = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(retType, false, typeDefs, pointerSize);
        } else {
            // return type is void
            objIt.next();
        }
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return new LLVMRetInstruction(value, debugLine);
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted SelectInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToSelectInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // identifier (needs valType to be converted, so do this later)
        LLVMParseLiteral id = (LLVMParseLiteral)objIt.next();
        // condition type (must be i1 or vector of i1)
        LLVMType condType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (condType.isBooleanOrVecOfBooleanType()) : "The condition type is neither i1 nor vector of i1!";
        }
        // condition value
        LLVMLiteral condition = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(condType, false, typeDefs, pointerSize);
        // first value type
        LLVMType valType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // first value
        LLVMLiteral val1 = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(valType, false, typeDefs, pointerSize);
        // second value type (must be the same as for the first value)
        LLVMType secondType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (valType.equals(secondType)) : "The types of the values are not equal!";
        }
        // second value
        LLVMLiteral val2 = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(valType, false, typeDefs, pointerSize);
        //        selectInstr.setValue2Literal(bLit);
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return new LLVMSelectInstruction(id.convertToIdentifier(valType), condition, val1, val2, debugLine);

    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted ShuffleVectorInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToShuffleVectorInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // identifier (needs resulting type to be converted, so do this later)
        LLVMParseLiteral id = (LLVMParseLiteral)objIt.next();
        // first vector type
        LLVMType vecType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // first vector literal
        LLVMLiteral vec1 = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(vecType, false, typeDefs, pointerSize);
        // second vector type (must be the same as the one of the first vector)
        LLVMType secondType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (vecType.isVectorType()) : "The vector is no vector!";
            assert (vecType.equals(secondType)) : "The vectors do not have the same type!";
        }
        // second vector literal
        LLVMLiteral vec2 = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(vecType, false, typeDefs, pointerSize);
        // mask type
        LLVMType maskType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (maskType.isVectorType()) : "Mask is no vector!";
        }
        // mask literal
        LLVMLiteral mask = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(maskType, false, typeDefs, pointerSize);
        // TODO check what happens if the length of the mask is longer than the sum of the lengths of the input vectors
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return
            new LLVMShuffleVectorInstruction(
                id.convertToIdentifier(
                    new LLVMVectorType(
                        vecType.getThisAsVectorType().getElementType(),
                        maskType.getThisAsVectorType().getLength()
                    )
                ),
                vec1,
                vec2,
                mask,
                debugLine
            );
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted StoreInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToStoreInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // volatile bit (ignored)
        objIt.next();
        // type which will be stored
        LLVMType valType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // value which will be stored
        LLVMLiteral value = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(valType, false, typeDefs, pointerSize);
        // address type
        LLVMType pointerType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // address
        LLVMLiteral pointer = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(pointerType, true, typeDefs, pointerSize);
        // alignment?
        LLVMLiteral alignment = null;
        if ((Boolean)objIt.next()) {
            alignment = ((LLVMParseLiteral)objIt.next()).convertToAlignment(pointerSize);
        }
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return new LLVMStoreInstruction(value, pointer, alignment, debugLine);
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted SwitchInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToSwitchInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // switch type (must be some int type)
        LLVMType switchType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (switchType.isIntType()) : "Switch type is no integer type!";
        }
        // value which will be stored
        LLVMLiteral value = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(switchType, false, typeDefs, pointerSize);
        // default label type
        LLVMType defaultLabelType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (defaultLabelType.isLabelType()) : "Label is no label!";
        }
        // default label value
        String defaultLabel = ((LLVMParseLiteral)objIt.next()).convertToLabelName();
        // read jump table
        int numOfJumpObjs = (Integer)objIt.next();
        if (Globals.useAssertions) {
            assert (numOfJumpObjs % 4 == 0) : "Number of jump objects is not dividable by 4!";
        }
        List<ImmutablePair<LLVMLiteral, String>> jumpList = new ArrayList<ImmutablePair<LLVMLiteral, String>>();
        for (int i = 0; i < numOfJumpObjs / 4; i++) {
            // jump value type
            LLVMType jumpType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
            if (Globals.useAssertions) {
                assert (jumpType.equals(switchType)) : "Jump type is not the same as switch type!";
            }
            // jump value
            LLVMLiteral jumpValue = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(switchType, false, typeDefs, pointerSize);
            // jump label type
            LLVMType jumpLabelType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
            if (Globals.useAssertions) {
                assert (jumpLabelType.isLabelType()) : "Label is no label!";
            }
            // jump label value
            String jumpLabel = ((LLVMParseLiteral)objIt.next()).convertToLabelName();
            jumpList.add(new ImmutablePair<LLVMLiteral, String>(jumpValue, jumpLabel));
        }
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return new LLVMSwitchInstruction(value, defaultLabel, ImmutableCreator.create(jumpList), debugLine);
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted UncondBrInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToUncondBrInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // destination type must be label
        LLVMType labelType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        if (Globals.useAssertions) {
            assert (labelType.isLabelType()) : "Label is no label!";
        }
        String labelName = ((LLVMParseLiteral)objIt.next()).convertToLabelName();
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return new LLVMUncondBrInstruction(labelName, debugLine);
    }

    /**
     * @param objIt An iterator of the instruction's parameters.
     * @param typeDefs The type definitions.
     * @param pointerSize The pointer size.
     * @return The converted VaArgInstruction.
     * @throws LLVMParseException If some parse error occurs.
     */
    private static LLVMInstruction convertToVaArgInstruction(
        Iterator<Object> objIt,
        Map<String, LLVMType> typeDefs,
        int pointerSize
    ) throws LLVMParseException {
        // identifier (needs argType to be converted, so do this later)
        LLVMParseLiteral id = (LLVMParseLiteral)objIt.next();
        // type of variable argument list
        LLVMType listType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        // variable argument list
        LLVMLiteral argList = ((LLVMParseLiteral)objIt.next()).convertToBasicLiteral(listType, false, typeDefs, pointerSize);
        // argument type which will be returned
        LLVMType argType = ((LLVMParseType)objIt.next()).convertToBasicType(typeDefs, pointerSize);
        int debugLine = -1;
        if (objIt.hasNext()) {
            LLVMParseLiteral next = (LLVMParseLiteral)objIt.next();
            if (next != null) {
                debugLine = next.convertToI32(pointerSize);
            }
        }
        return new LLVMVaArgInstruction(id.convertToIdentifier(argType), argList, debugLine);
    }

    /**
     * The type of the instruction.
     */
    private final LLVMInstructionType instrType;

    /**
     * The parameters of the instruction.
     */
    private final List<Object> objects;

    /**
     * True iff this instruction is a call to a debug intrinsic (llvm.dbg.*). Such instructions are not analyzed and are
     * dropped when converting to the basic block structure.
     */
    private boolean dbgIntrinsic = false;

    /**
     * For a llvm.dbg.declare intrinsic: the pointer (alloca) that the declared source variable lives in. May be
     * <code>null</code>.
     */
    private LLVMParseLiteral dbgDeclarePointer = null;

    /**
     * For a llvm.dbg.declare intrinsic: the index of the DILocalVariable debug metadata node bound to the pointer, or
     * -1 if none.
     */
    private int dbgDeclareLocalVarIndex = -1;

    /**
     * Creates an instruction of thhe specified type with no parameters.
     * @param instrTypeParam The type of the instruction.
     */
    public LLVMParseInstruction(LLVMInstructionType instrTypeParam) {
        this.instrType = instrTypeParam;
        this.objects = new ArrayList<Object>();
    }

    /**
     * Adds a parameter to this instruction.
     * @param param The parameter to add.
     */
    public void addParam(Object param) {
        this.objects.add(param);
    }

    /**
     * @return True iff this instruction is a call to a debug intrinsic (llvm.dbg.*).
     */
    public boolean isDbgIntrinsic() {
        return this.dbgIntrinsic;
    }

    public void setDbgIntrinsic(boolean dbgIntrinsic) {
        this.dbgIntrinsic = dbgIntrinsic;
    }

    /**
     * Records the binding of a llvm.dbg.declare intrinsic.
     * @param pointer The pointer (alloca) the source variable lives in.
     * @param localVarIndex The index of the bound DILocalVariable debug metadata node.
     */
    public void setDbgDeclare(LLVMParseLiteral pointer, int localVarIndex) {
        this.dbgDeclarePointer = pointer;
        this.dbgDeclareLocalVarIndex = localVarIndex;
    }

    /**
     * @return For a llvm.dbg.declare intrinsic: the pointer (alloca) the declared source variable lives in, or
     *         <code>null</code>.
     */
    public LLVMParseLiteral getDbgDeclarePointer() {
        return this.dbgDeclarePointer;
    }

    /**
     * @return For a llvm.dbg.declare intrinsic: the index of the bound DILocalVariable debug metadata node, or -1.
     */
    public int getDbgDeclareLocalVarIndex() {
        return this.dbgDeclareLocalVarIndex;
    }

    /**
     * This method converts an instruction from the parsing structure to an instruction
     * in basic structures (the basic structures are structures to work with).
     * The instruction in the parsing structure is a list of objects, which is constructed
     * in the parser and has to be interpreted in the right manner (which will be done in this method).
     * So if you change the grammar for instructions in the parser, you also have to change
     * the object interpretation in this method.
     * @param typeDefs Type definitions.
     * @param pointerSize The pointer size.
     * @return The converted instruction.
     * @throws LLVMParseException If the conversion is not successful because of a parse error.
     */
    public LLVMInstruction convertToBasicInstruction(Map<String, LLVMType> typeDefs, int pointerSize)
        throws LLVMParseException {
        switch (this.instrType) {
            case ALLOCA:
                return LLVMParseInstruction.convertToAllocaInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case BINARY:
                return LLVMParseInstruction.convertToBinaryInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case COND_BR:
                return LLVMParseInstruction.convertToCondBrInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case UNCOND_BR:
                return LLVMParseInstruction.convertToUncondBrInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case CALL:
                return LLVMParseInstruction.convertToCallInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case FLOAT_CMP:
                return LLVMParseInstruction.convertToFloatCmpInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case CONVERSION:
                return LLVMParseInstruction.convertToConversionInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case EXTRACTELEMENT:
                return LLVMParseInstruction.convertToExtractElementInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case EXTRACTVALUE:
                return LLVMParseInstruction.convertToExtractValueInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case GETELEMENTPTR:
                return LLVMParseInstruction.convertToGetElementPtrInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case INDIRECT_BR:
                return LLVMParseInstruction.convertToIndirectBrInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case INSERTELEMENT:
                return LLVMParseInstruction.convertToInsertElementInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case INSERTVALUE:
                return LLVMParseInstruction.convertToInsertValueInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case INT_CMP:
                return LLVMParseInstruction.convertToIntCmpInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case INVOKE:
                return LLVMParseInstruction.convertToInvokeInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case LOAD:
                return LLVMParseInstruction.convertToLoadInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case PHI:
                return LLVMParseInstruction.convertToPhiInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case RET:
                return LLVMParseInstruction.convertToReturnInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case SELECT:
                return LLVMParseInstruction.convertToSelectInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case SHUFFLEVECTOR:
                return LLVMParseInstruction.convertToShuffleVectorInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case STORE:
                return LLVMParseInstruction.convertToStoreInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case SWITCH:
                return LLVMParseInstruction.convertToSwitchInstruction(this.objects.iterator(), typeDefs, pointerSize);
            case UNREACHABLE:
                // nothing to convert here, an unreachable instruction has no parameters
                return new LLVMUnreachableInstruction();
            case UNWIND:
                // nothing to convert here, an unwind instruction has no parameters
                return new LLVMUnwindInstruction();
            case VAARG:
                return LLVMParseInstruction.convertToVaArgInstruction(this.objects.iterator(), typeDefs, pointerSize);
            default:
                // this point should never be reached
                throw new IllegalStateException("No suitable type found!");
        }
    }

    @Override
    public String toString() {
        return this.instrType.toString() + ":" + this.objects.toString();
    }

}
