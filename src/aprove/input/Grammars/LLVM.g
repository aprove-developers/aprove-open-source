/*   Type:        ANTLR
 *   Title:       LLVM grammar
 *   Description: A grammar definiton for LLVM programs
 *   Project:     AProVE
 *   Authors:     Janine Repke
 *   Copyright:   Copyright (c) 2011
 *   Department:  RWTH Aachen / Templergraben 55 / D-52056 Aachen
 */

grammar LLVM;

options {
  language=Java;
}

@header{
package aprove.input.Generated.llvm;

import aprove.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.input.Programs.llvm.parseStructures.*;
import aprove.input.Programs.llvm.parseStructures.literals.*;
import aprove.input.Programs.llvm.parseStructures.dataTypes.*;
import aprove.input.Programs.llvm.internalStructures.module.*;
}

// lexer imports
@lexer::header{
package aprove.input.Generated.llvm;
}   

// global member variable for global requests
@members{     
    LLVMParseModule module = new LLVMParseModule(); 
    int biggest_local_identifier = -1; // since llvm allows implicit labels based on the biggest local identifier already seen we track them here
}

module returns [LLVMParseModule llvmModule] 
    :   
        ( source_file
        | data_layout {module.setDataLayout($data_layout.dataLayout);}
        | triple {module.setTriple($triple.triple);}
        | global_variable_definition {module.addGlobalVariable($global_variable_definition.var);}
        | function_definition {module.addFunctionDefinition($function_definition.function);}
        | function_declaration {module.addFunctionDeclaration($function_declaration.function);}
        | type_definition {module.addTypeDefinition($type_definition.typeName, $type_definition.type);}
        | alias_definition {module.addAliasDefinition($alias_definition.aliasDefinition);} 
        | attribute_group
        | EXCLAMATION
            (
              ignore_information
            | debug_information {module.addDebugInformation($debug_information.debugInformation);}
            )
        )*
        EOF
        {
            llvmModule = module;
        }
    ;

source_file
  : SOURCEFILENAME ASSIGN STRING_LITERAL
  ;

data_layout returns [String dataLayout]
  : TARGET DATALAYOUT ASSIGN STRING_LITERAL
    { $dataLayout = $STRING_LITERAL.text;
    }
    ;
    
triple returns [String triple]
  : TARGET TRIPLE ASSIGN STRING_LITERAL
    { $triple = $STRING_LITERAL.text;
    }
    ;

global_variable_definition returns [LLVMParseVariable var] // also declaration
    :   GLOBAL_IDENTIFIER
        ASSIGN
        address_space?
    linkage_type?
    UNNAMED_ADDR?
    DSO_LOCAL?
    global_or_constant
    overall_type  // TODO: more types allowed?
    literal? // init value
    (COMMA section)?
    (COMMA alignment)?
    THREAD_LOCAL?
    (COMMA EXCLAMATION DEBUG debug_line)?
        {
          var = new LLVMParseVariable($GLOBAL_IDENTIFIER.text.substring(1), $overall_type.type);
          if ($address_space.literal != null) {
              var.setAddrSpace($address_space.literal);
          }
          if ($linkage_type.linkType != null) {
              var.setLinkageType($linkage_type.linkType);
          }
          var.setConstant($global_or_constant.isConstant);
          var.setTypeString($overall_type.text);
          if ($literal.literal != null) {
              var.setInitValueString($literal.text);
              var.setInitValue($literal.literal);
          }
          if ($section.literal != null) {
              var.setSection($section.literal);
          }
          if ($alignment.literal != null) {
              var.setAlignment($alignment.literal);
          }
          if ($THREAD_LOCAL != null ) {
              var.setThreadLocal(true);
          }
        }
    ;


alias_definition returns [LLVMParseAliasDefinition aliasDefinition]
@init{
    aliasDefinition = new LLVMParseAliasDefinition(); 
} 
    :   g1=GLOBAL_IDENTIFIER // alias name
        ASSIGN
        ALIAS
    alias_linkage_type? 
    visibility_type?
    overall_type // type of the alias value
    g2=GLOBAL_IDENTIFIER // value which will be aliase
    {
        aliasDefinition.setAliasName($g1.text.substring(1));
          if($alias_linkage_type.linkType != null) {
            aliasDefinition.setLinkageType($alias_linkage_type.linkType);
          } 
          if($visibility_type.visType != null) {
            aliasDefinition.setVisType($visibility_type.visType);
          } 

          aliasDefinition.setAliasedType($overall_type.type);
          aliasDefinition.setAliasedName($g2.text.substring(1));
        }
    ; 
    
    
attribute_group
    :  
        ATTRIBUTES
        HASH
        INT_NUMBER
        ASSIGN
        OPENC
          (ALLOCSIZE OPENP INT_NUMBER CLOSEP)*
          function_attribute*
          (STRING_LITERAL (ASSIGN STRING_LITERAL)?)*
        CLOSEC
    ;


debug_information returns [LLVMParseDebugInformation debugInformation]
@init{
    debugInformation = new LLVMParseDebugInformation();
}
    :
        i=int_literal
        ASSIGN
        DISTINCT?
        EXCLAMATION
        (
          DIEXPRESSION
        |
          (
            OPENC
              (
                STRING_LITERAL | DEBUG_IDENTIFIER | int_literal | label1_or_int
              | overall_type literal | NULL
              | COMMA | EXCLAMATION
              )*
            CLOSEC
          )
        |
          (
            'DISubprogram'
            OPENP
              (
                ((
                  'name'
                  COLON
                  fname=STRING_LITERAL
                )
                | (
                  'line'
                  COLON
                  line=int_literal
                )
                | (
                  (DEBUG_IDENTIFIER | TYPE | ALIGN)
                  COLON
                  EXCLAMATION?
                  (STRING_LITERAL | DEBUG_IDENTIFIER | int_literal | label1_or_int | overall_type | DIEXPRESSION)
                  ('|' (STRING_LITERAL | DEBUG_IDENTIFIER | int_literal | label1_or_int | overall_type | DIEXPRESSION))*
                  (GLOBAL_IDENTIFIER | LOCAL_IDENTIFIER)?
                ))
                COMMA?
              )*
            CLOSEP
          | 'DILocation'
            OPENP
              (
                ((
                  'line'
                  COLON
                  line=int_literal
                )
                | (
                  (DEBUG_IDENTIFIER | TYPE | ALIGN)
                  COLON
                  EXCLAMATION?
                  (STRING_LITERAL | DEBUG_IDENTIFIER | int_literal | label1_or_int | overall_type | DIEXPRESSION)
                  (GLOBAL_IDENTIFIER | LOCAL_IDENTIFIER)?
                ))
                COMMA?
              )*
            CLOSEP
          | kind=DEBUG_IDENTIFIER
            {debugInformation.setKind($kind.text);}
            OPENP
              (
                k1=di_key
                (
                  COLON
                  v1=di_value
                  {debugInformation.addField($k1.text, $v1.text);}
                )?
                (
                  COMMA
                  k2=di_key
                  (
                    COLON
                    v2=di_value
                    {debugInformation.addField($k2.text, $v2.text);}
                  )?
                )*
              )?
            CLOSEP
          )
        )
        {
            debugInformation.setIndex($i.literal);
            debugInformation.setFunctionName($fname.text);
            debugInformation.setCLine($line.literal);
        }
    ;


// the key of a field in a debug metadata node (e.g. "name", "encoding", "type", "baseType")
di_key
    :   ('name' | 'line' | DEBUG_IDENTIFIER | TYPE | ALIGN)
    ;

// the value of a field in a debug metadata node (e.g. "DW_ATE_unsigned", "!12", "32", "\"unsigned int\"");
// the value text is later retrieved via the rule's matched-input text
di_value
    :   (~(COMMA | OPENP | CLOSEP))*
        (
          OPENP
            (~(OPENP | CLOSEP))*
          CLOSEP
        )*
    ;


ignore_information
    :
        DEBUG_IDENTIFIER
        ASSIGN
        EXCLAMATION
        OPENC
          EXCLAMATION INT_NUMBER
          (COMMA EXCLAMATION INT_NUMBER)*
        CLOSEC
    ;


function_definition returns [LLVMParseFunctionDefinition function = new LLVMParseFunctionDefinition();]
    :   DEFINE
        DSO_LOCAL?
        linkage_type?
        visibility_type?
        calling_convention?
        full_type_n // return type with optional parameter attributes
        GLOBAL_IDENTIFIER
        { biggest_local_identifier = -1;}
        OPENP
            (
             (
               f1=full_type_r (l1=LOCAL_IDENTIFIER)?
                 {
                   if ($l1 != null) {
                     $f1.param.setName($l1.text.substring(1));
                   } else {
                     biggest_local_identifier++;
                     $f1.param.setName(String.valueOf(biggest_local_identifier));
                   }
                   function.addParameter($f1.param);
                 }
               (COMMA f2=full_type_r (l2=LOCAL_IDENTIFIER)?
                 {
                   if ($l2 != null) {
                     $f2.param.setName($l2.text.substring(1));
                   } else {
                     biggest_local_identifier++;
                     $f2.param.setName(String.valueOf(biggest_local_identifier));
                   }
                   function.addParameter($f2.param);
                 }
               )*
               (COMMA argList = DOTS )?
             )?
            |
            (argList = DOTS)
            )
        CLOSEP // argument list (type and variable name), possibly empty
        (HASH INT_NUMBER)*
        (EXCLAMATION DEBUG debug_line)?
        (function_attribute {function.addAttribute($function_attribute.attribute);} )*
        section?
        alignment?
        (GC (garColl = STRING_LITERAL| constant_expression))? // garbage collector name
        OPENC
        (
        {
            biggest_local_identifier++;
            LLVMParseBlock actBlock = new LLVMParseBlock(String.valueOf(biggest_local_identifier));
        }
            (label1_or_int
                {
                    actBlock = new LLVMParseBlock($label1_or_int.text);
                    biggest_local_identifier--; // blocks with own labels do not count
                } COLON)?
            (non_term_instruction { actBlock.addInstruction($non_term_instruction.instr); })*
            term_instruction {actBlock.addInstruction($term_instruction.instr);}
            {function.addBlock(actBlock);}
        )+  //instructions TODO
        CLOSEC
        {
      function.setLinkageType($linkage_type.linkType);
      function.setVisType($visibility_type.visType);
      function.setCallConv($calling_convention.callConv);
      function.setReturnType($full_type_n.returnParam);
      function.setName($GLOBAL_IDENTIFIER.text.substring(1)); // delete leading @-sign
      function.setAlignment($alignment.literal);
      function.setSection($section.literal);
      if ($argList != null) {
        function.setVariableLength(true);
      }
      if (garColl != null) {
        function.setGarColl($garColl.text);
      }
      function.setDebugLine($debug_line.literal);
        }
    ;

function_declaration returns [LLVMParseFunctionDeclaration function = new LLVMParseFunctionDeclaration();]
    :   DECLARE
        DSO_LOCAL?
        linkage_type?
        visibility_type?
        calling_convention?
        full_type_n
        GLOBAL_IDENTIFIER
        OPENP
            (
             (f1=full_type_r IMMARG? {function.addParameter($f1.param);}
               (COMMA f2=full_type_r IMMARG? {function.addParameter($f2.param);})*
               (COMMA argList = DOTS )?
             )?
             |
             (argList=DOTS )
            )
        CLOSEP
        (HASH INT_NUMBER)*
        (function_attribute {function.addAttribute($function_attribute.attribute);} )*
        alignment?
        (garColl = STRING_LITERAL| constant_expression)? //garbage collector name
        {
          function.setLinkageType($linkage_type.linkType);
          function.setVisType($visibility_type.visType);
          function.setCallConv($calling_convention.callConv);
          function.setReturnType($full_type_n.returnParam);
          function.setName($GLOBAL_IDENTIFIER.text.substring(1)); // delete leading @-sign
          function.setAlignment($alignment.literal);
          if ($argList != null) {
            function.setVariableLength(true);
          }
          if (garColl != null) {
            function.setGarColl($garColl.text);
          }
         }
    ;


/**
 * specifies a named aliase for a type, it can only appear at global level (not in function definitions) the name determines the scope
 * for example: %newType_0 and %newType_1 are the same types but defined in different functions
 */
type_definition returns [String typeName, LLVMParseType type]
    :   LOCAL_IDENTIFIER 
        ASSIGN
        TYPE
        type_with_pointer_and_function
        {
            $typeName = $LOCAL_IDENTIFIER.text.substring(1); // remove leading per cent sign
            $type = $type_with_pointer_and_function.type;
        }
    ;

address_space returns [LLVMParseLiteral literal]
    :   ADDRSPACE OPENP literal CLOSEP
     { 
       $literal = $literal.literal;
     }
    ;

alignment returns [LLVMParseLiteral literal]    
    :   ALIGN literal // TODO: the number should be a power of 2
     {
        $literal = $literal.literal;
     }
    ;

debug_line returns [LLVMParseLiteral literal]
    :   EXCLAMATION literal
     {
        $literal = $literal.literal;
     }
    ;
    
section returns [LLVMParseLiteral literal]
    :    SECTION literal // literal should be a string
     { 
            $literal = $literal.literal;
     }
    ;


// TODO: add a rule for aliases and named metadata, also for: module-level inline assembly, data layout. pointer aliasing rules, volatile memory access

function_attribute returns [LLVMFunctionAttribute attribute]
    @init{
        LLVMParseType type = new LLVMParseIntType(32);
    }
    :   ALIGNSTACK OPENP INT_NUMBER CLOSEP {attribute = new LLVMFunctionAttribute(Integer.parseInt($INT_NUMBER.text));}
    |   ADDRESSSAFETY {attribute = new LLVMFunctionAttribute(LLVMFunctionAttributeType.ADDRESS_SAFETY);}
    |   ALWAYSINLINE {attribute = new LLVMFunctionAttribute(LLVMFunctionAttributeType.ALWAYSINLINE);}
    |   ARGMEMONLY
    |   INLINEHINT {attribute = new LLVMFunctionAttribute(LLVMFunctionAttributeType.INLINEHINT);}
    |   NAKED {attribute = new LLVMFunctionAttribute(LLVMFunctionAttributeType.NAKED);}
    |   NODUPLICATE {attribute = new LLVMFunctionAttribute(LLVMFunctionAttributeType.NODUPLICATE);}
    |   NOIMPLICITFLOAT {attribute = new LLVMFunctionAttribute(LLVMFunctionAttributeType.NOIMPLICITFLOAT);}
    |   NOINLINE {attribute = new LLVMFunctionAttribute(LLVMFunctionAttributeType.NOINLINE);}
    |   NOLAZYBIND {attribute = new LLVMFunctionAttribute(LLVMFunctionAttributeType.NOLAZYBIND);}
    |   NOREDZONE {attribute = new LLVMFunctionAttribute(LLVMFunctionAttributeType.NOREDZONE);}
    |   NORETURN {attribute = new LLVMFunctionAttribute(LLVMFunctionAttributeType.NORETURN);}
    |   NOUNWIND {attribute = new LLVMFunctionAttribute(LLVMFunctionAttributeType.NOUNWIND);}
    |   OPTSIZE {attribute = new LLVMFunctionAttribute(LLVMFunctionAttributeType.OPTSIZE);}
    |   READNONE {attribute = new LLVMFunctionAttribute(LLVMFunctionAttributeType.READNONE);}
    |   READONLY {attribute = new LLVMFunctionAttribute(LLVMFunctionAttributeType.READONLY);}
    |   RETURNSTWICE {attribute = new LLVMFunctionAttribute(LLVMFunctionAttributeType.RETURNS_TWICE);}
    |   SSP {attribute = new LLVMFunctionAttribute(LLVMFunctionAttributeType.SSP);}
    |   SSPREQ {attribute = new LLVMFunctionAttribute(LLVMFunctionAttributeType.SSPREQ);}
    |   UWTABLE {attribute = new LLVMFunctionAttribute(LLVMFunctionAttributeType.UWTABLE);}
    |   WRITEONLY
    |   OPTNONE
    |   SPECULATABLE
    |   WILLRETURN
    ;

// functions, calls and invokes can have an optional calling convention
calling_convention returns [LLVMCallingConvention callConv]
    :   CCC {callConv = new LLVMCallingConvention(LLVMCallingConventionType.CCC);}
    |   FASTCC {callConv = new LLVMCallingConvention(LLVMCallingConventionType.FASTCC);}
    |   COLDCC {callConv = new LLVMCallingConvention(LLVMCallingConventionType.COLDCC);}
    |   CC10 {callConv = new LLVMCallingConvention(LLVMCallingConventionType.CC_10);}
    |   CC11 {callConv = new LLVMCallingConvention(LLVMCallingConventionType.CC_11);}
    |   CC_NUMBER {callConv = new LLVMCallingConvention(Integer.parseInt($CC_NUMBER.text.substring(2)));}
    ;
    
global_or_constant returns [boolean isConstant]
  : GLOBAL {$isConstant = false;}
  | CONSTANT {$isConstant = true;}
  ;

linkage_type returns [LLVMLinkageType linkType]// all global variables and functions have one of the following types of linkage
    :   PRIVATE {$linkType = LLVMLinkageType.PRIVATE;}
    |   LINKERPRIVATE {$linkType = LLVMLinkageType.LINKER_PRIVATE;}
    |   LINKERPRIVATEWEAK {$linkType = LLVMLinkageType.LINKER_PRIVATE_WEAK;}
    |   LINKERPRIVATEWEAKDEFAUTO {$linkType = LLVMLinkageType.LINKER_PRIVATE_WEAK_DEF_AUTO;}
    |   INTERNAL {$linkType = LLVMLinkageType.INTERNAL;}
    |   AVAILABLEEXTERNALLY {$linkType = LLVMLinkageType.AVAILABLE_EXTERNALLY;}
    |   LINKONCE {$linkType = LLVMLinkageType.LINKONCE;}
    |   WEAK {$linkType = LLVMLinkageType.WEAK;}
    |   COMMON {$linkType = LLVMLinkageType.COMMON;}
    |   APPENDING {$linkType = LLVMLinkageType.APPENDING;}
    |   EXTERNWEAK {$linkType = LLVMLinkageType.EXTERN_WEAK;}
    |   LINKONCEODR {$linkType = LLVMLinkageType.LINKONCE_ODR;}
    |   WEAKODR {$linkType = LLVMLinkageType.WEAK_ODR;}
    |   DLLIMPORT {$linkType = LLVMLinkageType.DLLIMPORT;}   // special windows linkage types
    |   DLLEXPORT {$linkType = LLVMLinkageType.DLLEXPORT;} // special windows linkage types
    |   EXTERNAL {$linkType = LLVMLinkageType.EXTERNAL;}
    ;   // if none of this is used, theglobal is externally visible

alias_linkage_type returns [LLVMAliasLinkageType linkType]// alias definitions have different linkage types
    :   INTERNAL {$linkType = LLVMAliasLinkageType.EXTERNAL;}
    |   EXTERNAL {$linkType = LLVMAliasLinkageType.INTERNAL;}
    |   WEAK {$linkType = LLVMAliasLinkageType.WEAK;}
    |   WEAKODR {$linkType = LLVMAliasLinkageType.WEAK_ODR;}
;

parameter_attribute returns [LLVMParameterAttribute attribute]
    :   ZEROEXT {attribute = LLVMParameterAttribute.ZEROEXT;}
    |   SIGNEXT {attribute = LLVMParameterAttribute.SIGNEXT;}
    |   INREG {attribute = LLVMParameterAttribute.INREG;}
    |   BYVAL {attribute = LLVMParameterAttribute.BYVAL;}
    |   SRET {attribute = LLVMParameterAttribute.SRET;}
    |   NOALIAS {attribute = LLVMParameterAttribute.NOALIAS;}
    |   NOCAPTURE {attribute = LLVMParameterAttribute.NOCAPTURE;}
    |   NEST {attribute = LLVMParameterAttribute.NEST;}
    |   NONNULL {attribute = LLVMParameterAttribute.NONNULL;}
    |   READONLY {attribute = LLVMParameterAttribute.READONLY;}
    |   WRITEONLY
    ;

// all global variable and functions have one of the following visibility styles
visibility_type returns [LLVMVisibilityType visType]
    :   DEFAULT {visType = LLVMVisibilityType.DEFAULT;}
    |   HIDDEN {visType = LLVMVisibilityType.HIDDEN;}
    |   PROTECTED {visType = LLVMVisibilityType.PROTECTED;}
    ;


/***** types *****/

// type_with_pointer_function_void
overall_type returns [LLVMParseType type]   // the definiton of the return instruction requires a difference between void and other types
    :   type_with_pointer_and_function {$type = $type_with_pointer_and_function.type;}
    ;

// type_with_pointer_function_void (no metadata)
overall_type_no_metadata returns [LLVMParseType type]   // the definiton of the return instruction requires a difference between void and other types
    :   type_with_pointer_and_function_no_metadata {$type = $type_with_pointer_and_function_no_metadata.type;}
    ;
    
// same type as  type_with_pointer_function_void but without void
type_with_pointer_and_function  returns [LLVMParseType type]
@init {
    LLVMParseType lastType = null; // last function type or pointer to a function
    int pointerCount = 0; 
    boolean voidType = false;
}
    :   (returnType = type_with_pointer | void_type {voidType = true;} )  // type_with_pointer_and_function here not possible, because of left recursion
        (
            { LLVMParseFunctionType fnType = new LLVMParseFunctionType(); // actual function
                if(lastType ==  null) { // first function gets return type, other functions have a function as return type
                    if(voidType) {
                        fnType.setReturnType($void_type.type);
                    } else {
                        fnType.setReturnType($returnType.type);
                    }
                    voidType = false;
                }
            }
            OPENP
                (
                    (
                        param1 = type_with_pointer_and_function {fnType.addParameter($param1.type);} 
                        (COMMA param2 = type_with_pointer_and_function {fnType.addParameter($param2.type);})*
                        (COMMA va_arg = DOTS)?
                    )
                    |
                    (   va_arg = DOTS )?
                )
            CLOSEP  (STAR {pointerCount++;})* // for function pointers - TODO: are this always pointer?
            {
                if($va_arg != null) {
                    fnType.setVarArgument(true); // variable argument list
                }
                if(lastType != null) {
                    fnType.setReturnType(lastType); // this function has a function as return type
                }
                lastType = fnType;
                
                
                while(pointerCount!=0) {  // it's a function pointer
                    pointerCount--;
                    lastType = new LLVMParsePointerType(lastType);
                }
                /*
                if(pointer != null) {
                    lastType = new LLVMParsePointerType(fnType);
                }*/
            }
        )*
        {
            if(lastType != null) {
                $type = lastType; // function type
            } else {
              if(voidType) { 
                $type = $void_type.type;
              } else {
                    $type = $returnType.type; // no function type
                }
                voidType = false;
            }
        }
    ;
    
// same type as  type_with_pointer_and_function but without metadata
type_with_pointer_and_function_no_metadata  returns [LLVMParseType type]
@init {
    LLVMParseType lastType = null; // last function type or pointer to a function
    int pointerCount = 0; 
    boolean voidType = false;
}
    :   (returnType = type_with_pointer_no_metadata | void_type {voidType = true;} )  // type_with_pointer_and_function here not possible, because of left recursion
        (
            { LLVMParseFunctionType fnType = new LLVMParseFunctionType(); // actual function
                if(lastType ==  null) { // first function gets return type, other functions have a function as return type
                    if(voidType) {
                        fnType.setReturnType($void_type.type);
                    } else {
                        fnType.setReturnType($returnType.type);
                    }
                    voidType = false;
                }
            }
            OPENP
                (
                    (
                        param1 = type_with_pointer_and_function_no_metadata {fnType.addParameter($param1.type);} 
                        (COMMA param2 = type_with_pointer_and_function_no_metadata {fnType.addParameter($param2.type);})*
                        (COMMA va_arg = DOTS)?
                    )
                    |
                    (   va_arg = DOTS )?
                )
            CLOSEP  (STAR {pointerCount++;})* // for function pointers - TODO: are this always pointer?
            {
                if($va_arg != null) {
                    fnType.setVarArgument(true); // variable argument list
                }
                if(lastType != null) {
                    fnType.setReturnType(lastType); // this function has a function as return type
                }
                lastType = fnType;
                
                
                while(pointerCount!=0) {  // it's a function pointer
                    pointerCount--;
                    lastType = new LLVMParsePointerType(lastType);
                }
                /*
                if(pointer != null) {
                    lastType = new LLVMParsePointerType(fnType);
                }*/
            }
        )*
        {
            if(lastType != null) {
                $type = lastType; // function type
            } else {
              if(voidType) { 
                $type = $void_type.type;
              } else {
                    $type = $returnType.type; // no function type
                }
                voidType = false;
            }
        }
    ;

type_with_pointer returns [LLVMParseType type]
  @init {
    LLVMParsePointerType pointerType;
  }
    :   general_type {$type = $general_type.type;} 
      (address_space? STAR
       {
        pointerType = new LLVMParsePointerType($type);  
      pointerType.setAddressSpace($address_space.literal);
        $type = pointerType;
       }
      )* // TODO: no pointers allowed to void or labels - semantic
    ;

type_with_pointer_no_metadata returns [LLVMParseType type]
  @init {
    LLVMParsePointerType pointerType;
  }
    :   general_type_no_metadata {$type = $general_type_no_metadata.type;} 
      (address_space? STAR
       {
        pointerType = new LLVMParsePointerType($type);  
      pointerType.setAddressSpace($address_space.literal);
        $type = pointerType;
       }
      )* // TODO: no pointers allowed to void or labels - semantic
    ;

general_type    returns [LLVMParseType type]
  : primitive_type  {$type = $primitive_type.type;}
    |   complex_type  {$type = $complex_type.type;}
    |   LOCAL_IDENTIFIER {$type = new LLVMParseNamedType($LOCAL_IDENTIFIER.text.substring(1));} // removing leading percent-sign}
    ;

general_type_no_metadata    returns [LLVMParseType type]
  : primitive_type_no_metadata  {$type = $primitive_type_no_metadata.type;}
    |   complex_type  {$type = $complex_type.type;}
    |   LOCAL_IDENTIFIER {$type = new LLVMParseNamedType($LOCAL_IDENTIFIER.text.substring(1));} // removing leading percent-sign}
    ;

return_type returns [LLVMParseType type] // same es type but without label type
    :   primitive_type_no_label_no_void {$type = $primitive_type_no_label_no_void.type;}
    |   complex_type {$type = $complex_type.type;}
    |   LOCAL_IDENTIFIER {$type = new LLVMParseNamedType($LOCAL_IDENTIFIER.text.substring(1));} // removing leading percent-sign}
    ;

return_type_no_metadata returns [LLVMParseType type] // same es type but without label type
    :   primitive_type_no_label_no_void_no_metadata {$type = $primitive_type_no_label_no_void_no_metadata.type;}
    |   complex_type {$type = $complex_type.type;}
    |   LOCAL_IDENTIFIER {$type = new LLVMParseNamedType($LOCAL_IDENTIFIER.text.substring(1));} // removing leading percent-sign}
    ;
    
primitive_type returns [LLVMParseType type] // all primitive types including label type
    :   primitive_type_no_label_no_void {$type = $primitive_type_no_label_no_void.type;}
    |   label_type {$type = $label_type.type;}
    ;
    
primitive_type_no_metadata returns [LLVMParseType type] // all primitive types including label type
    :   primitive_type_no_label_no_void_no_metadata {$type = $primitive_type_no_label_no_void_no_metadata.type;}
    |   label_type {$type = $label_type.type;}
    ;
    
primitive_type_no_label_no_void returns [LLVMParseType type]    // primitive type without label type and void
    :   int_type {$type = $int_type.type;}
    |   float_type {$type = $float_type.type;}
    |   metadata_type {$type = $metadata_type.type;}
    ;
    
primitive_type_no_label_no_void_no_metadata returns [LLVMParseType type]    // primitive type without label type and void
    :   int_type {$type = $int_type.type;}
    |   float_type {$type = $float_type.type;}
    ;
    
// types of  derived data structures
complex_type returns [LLVMParseType type] 
    :   array_type {$type = $array_type.type;}
    |   structure_type {$type = $structure_type.type;}
    |   packed_structure_type {$type = $packed_structure_type.type;}
    |   vector_type {$type = $vector_type.type;}
//  |   opaque_type // TODO implement this type
    ;


first_class_type_no_pointer returns [LLVMParseType type]// a subset of  some particular types, which are needed for better diffeerentiation in the parser
    :   int_type {$type = $int_type.type;}
    |   float_type {$type = $float_type.type;}
    |   label_type {$type = $label_type.type;}
    |   array_type {$type = $array_type.type;}
    |   structure_type {$type = $structure_type.type;}
    |   vector_type {$type = $vector_type.type;}
    |   LOCAL_IDENTIFIER {$type = new LLVMParseNamedType($LOCAL_IDENTIFIER.text.substring(1));} // removing leading percent-sign}
//  |   metadata_type // TODO:  metadata
    ;   

array_type returns [LLVMParseArrayType type]    
    : OPENB literal TIMES overall_type CLOSEB
      {$type = new LLVMParseArrayType($overall_type.type, $literal.literal);}
    ;

structure_type returns [LLVMParseStructureType type = new LLVMParseStructureType();]
    :   OPENC
       (t1 = overall_type {$type.addElementType($t1.type);})?
       (COMMA t2 = overall_type {$type.addElementType($t2.type);} )*
       CLOSEC
    ;

// a structure without padding  
packed_structure_type   returns [LLVMParsePackedStructureType type = new LLVMParsePackedStructureType();]
    :   OPENA OPENC
       t1 = type_with_pointer {$type.addElementType($t1.type);}
       (COMMA t2 = type_with_pointer {$type.addElementType($t2.type);})*
       CLOSEC CLOSEA
    ;

vector_type returns [LLVMParseVectorType type]
@init{
        LLVMParseType elementType = null;
    }   
    :   OPENA (int_literal | constant_expression)
        TIMES
        (   primitive_type {elementType = $primitive_type.type;}
            |
            LOCAL_IDENTIFIER {elementType = new LLVMParseNamedType($LOCAL_IDENTIFIER.text.substring(1));}
        )
        CLOSEA
        {
      if ($int_literal.literal != null) {
        $type = new LLVMParseVectorType(elementType, $int_literal.literal);
      } else {
        $type = new LLVMParseVectorType(elementType, $constant_expression.literal);
      }
    }
  ;

// type with optional parameters in normal order, used for return parameters
full_type_n returns [LLVMParseFunctionParameter returnParam = new LLVMParseFunctionParameter();]
    :   (parameter_attribute {returnParam.addAttribute($parameter_attribute.attribute);})*
      overall_type
     {
       returnParam.setType($overall_type.type);
     }
    ;


// type with optional parameters, in reverse order, used for functions parameters
full_type_r returns [LLVMParseFunctionParameter param = new LLVMParseFunctionParameter();]
    :  overall_type
       (parameter_attribute {param.addAttribute($parameter_attribute.attribute);} )*
   {
     param.setType($overall_type.type);
   }
    ;


// type with optional parameters (no metadata), in reverse order, used for functions parameters
full_type_r_no_metadata returns [LLVMParseFunctionParameter param = new LLVMParseFunctionParameter();]
    :  overall_type_no_metadata
       (parameter_attribute {param.addAttribute($parameter_attribute.attribute);} )*
   {
     param.setType($overall_type_no_metadata.type);
   }
    ;


/********** literals **********/

literal returns [LLVMParseLiteral literal]  // a literal or constant    
    :   basic_literal {$literal = $basic_literal.literal;}
    |   constant_expression {$literal = $constant_expression.literal;} 
    | identifier {$literal = $identifier.literal;}
    ;

basic_literal returns [LLVMParseLiteral literal]
    :   complex_literal {$literal = $complex_literal.literal;}
    |   simple_literal  {$literal = $simple_literal.literal;}
    ;

simple_literal returns [LLVMParseLiteral literal]
    :   int_literal {$literal = $int_literal.literal;}
    |   fp_literal {$literal = $fp_literal.literal;}
    |   string_literal {$literal = $string_literal.literal;}
    | special_string_literal {$literal = $special_string_literal.literal;}
    |   NULL {$literal = new LLVMParseNullLiteral();}
    |   undef_literal {$literal = $undef_literal.literal;} // the string can be used anywhere a constant is expected
    ;

complex_literal returns [LLVMParseLiteral literal]
    :   array_literal {$literal = $array_literal.literal;}
    |   structure_literal {$literal = $structure_literal.literal;}
    |   vector_literal {$literal = $vector_literal.literal;}
    |   zero_literal {$literal = $zero_literal.literal;}
    ;

structure_literal returns [LLVMParseStructureLiteral literal = new LLVMParseStructureLiteral();]
@init{
        Pair<LLVMParseType, LLVMParseLiteral> element;
    }
    :   OPENC
            (
                t1=overall_type l1=literal
                {
                    element = new Pair<LLVMParseType, LLVMParseLiteral>($t1.type, $l1.literal);
                    literal.addElement(element);
                }
                (
                    COMMA t2=overall_type l2=literal
                    {
                        element = new Pair<LLVMParseType, LLVMParseLiteral>($t2.type, $l2.literal);
                        literal.addElement(element);
                    }
                )*
            )
        CLOSEC
    ;

array_literal returns [LLVMParseArrayLiteral literal = new LLVMParseArrayLiteral();]
@init{
        Pair<LLVMParseType, LLVMParseLiteral> element = null; 
}
    :   OPENB
        (
            t1 = overall_type l1 = literal
            {
                    element = new Pair<LLVMParseType, LLVMParseLiteral>($t1.type, $l1.literal);
                    literal.addElement(element);
            }
            (
                COMMA t2 = overall_type l2 = literal
                {
                    element = new Pair<LLVMParseType, LLVMParseLiteral>($t2.type, $l2.literal);
                    literal.addElement(element);
                }
            )*
        )
        CLOSEB
    ;

vector_literal returns [LLVMParseVectorLiteral literal = new LLVMParseVectorLiteral();]
@init{
        Pair<LLVMParseType, LLVMParseLiteral> element;
    }
    :   OPENA
        (
            t1 = type_with_pointer l1 = literal
            {
                    element = new Pair<LLVMParseType, LLVMParseLiteral>($t1.type, $l1.literal);
                    literal.addElement(element);
            }
            (
                COMMA t2= type_with_pointer l2 = literal
                {
                    element = new Pair<LLVMParseType, LLVMParseLiteral>($t2.type, $l2.literal);
                    literal.addElement(element);
                }
            )*
        )
        CLOSEA
    ;

zero_literal returns [LLVMParseLiteral literal = new LLVMZeroInitializer();]
    :   ZEROINITIALIZER
    ;

/** Identifier **/


init_identifier returns [LLVMParseLiteral literal]
    :   GLOBAL_IDENTIFIER {$literal = new LLVMParseVariableLiteral($GLOBAL_IDENTIFIER.text.substring(1),LLVMVariableScope.GLOBAL);}
    |   LOCAL_IDENTIFIER {
        $literal = new LLVMParseVariableLiteral($LOCAL_IDENTIFIER.text.substring(1),LLVMVariableScope.LOCAL);
        try {
            int sym = Integer.parseInt($LOCAL_IDENTIFIER.text.substring(1));
            if (sym > biggest_local_identifier){ biggest_local_identifier = sym; }
        } catch (java.lang.NumberFormatException e){}
    }
    ;

identifier returns [LLVMParseLiteral literal]   
    :   GLOBAL_IDENTIFIER {$literal = new LLVMParseVariableLiteral($GLOBAL_IDENTIFIER.text.substring(1),LLVMVariableScope.GLOBAL);}
    |   LOCAL_IDENTIFIER {
        $literal = new LLVMParseVariableLiteral($LOCAL_IDENTIFIER.text.substring(1),LLVMVariableScope.LOCAL);
    }
    ;

/** Instructions **/

non_term_instruction    returns [LLVMParseInstruction instr]
    :   instruction_alloca {instr = $instruction_alloca.instr;}
    |   instruction_binary {instr = $instruction_binary.instr;}
    |   instruction_call {instr = $instruction_call.instr;}
    |   instruction_cmp_int {instr = $instruction_cmp_int.instr;}
    |   instruction_cmp_float {instr = $instruction_cmp_float.instr;}
    |   instruction_conversion {instr = $instruction_conversion.instr;}
    |   instruction_extractelement {instr = $instruction_extractelement.instr;}
    |   instruction_extractvalue {instr = $instruction_extractvalue.instr;}
    |   instruction_getelementptr {instr = $instruction_getelementptr.instr;}
    |   instruction_insertelement {instr = $instruction_insertelement.instr;}
    |   instruction_insertvalue {instr = $instruction_insertvalue.instr;}
    |   instruction_load {instr = $instruction_load.instr;}
    |   instruction_phi {instr = $instruction_phi.instr;}
    |   instruction_select {instr = $instruction_select.instr;}
    |   instruction_shufflevector {instr = $instruction_shufflevector.instr;}
    |   instruction_store {instr = $instruction_store.instr;}
    |   instruction_vaarg {instr = $instruction_vaarg.instr;}
    |   instruction_unwind {instr = $instruction_unwind.instr;}
    ;

term_instruction    returns [LLVMParseInstruction instr]
    :   instruction_br {instr = $instruction_br.instr;}
    |   instruction_indirect_br {instr = $instruction_indirect_br.instr;}
    |   instruction_invoke {instr = $instruction_invoke.instr;}
    |   instruction_ret {instr = $instruction_ret.instr;}
    |   instruction_switch {instr = $instruction_switch.instr;}
    |   instruction_unreachable {instr = $instruction_unreachable.instr;}
    ;

instruction returns [LLVMParseInstruction instr]
    :   instruction_alloca {instr = $instruction_alloca.instr;}
    |   instruction_binary {instr = $instruction_binary.instr;}
    |   instruction_br {instr = $instruction_br.instr;}
    |   instruction_call {instr = $instruction_call.instr;}
    |   instruction_cmp_int {instr = $instruction_cmp_int.instr;}
    |   instruction_cmp_float {instr = $instruction_cmp_float.instr;}
    |   instruction_conversion {instr = $instruction_conversion.instr;}
    |   instruction_extractelement {instr = $instruction_extractelement.instr;}
    |   instruction_extractvalue {instr = $instruction_extractvalue.instr;}
    |   instruction_getelementptr {instr = $instruction_getelementptr.instr;}
    |   instruction_insertelement {instr = $instruction_insertelement.instr;}
    |   instruction_insertvalue {instr = $instruction_insertvalue.instr;}
    | instruction_indirect_br {instr = $instruction_indirect_br.instr;}
    | instruction_invoke {instr = $instruction_invoke.instr;}
    |   instruction_load {instr = $instruction_load.instr;}
    |   instruction_phi {instr = $instruction_phi.instr;}
    |   instruction_ret {instr = $instruction_ret.instr;}
    |   instruction_select {instr = $instruction_select.instr;}
    |   instruction_shufflevector {instr = $instruction_shufflevector.instr;}
    |   instruction_store {instr = $instruction_store.instr;}
    |   instruction_switch {instr = $instruction_switch.instr;}
    |   instruction_vaarg {instr = $instruction_vaarg.instr;}
    |   instruction_unreachable {instr = $instruction_unreachable.instr;}
    |   instruction_unwind {instr = $instruction_unwind.instr;}
    ;

instruction_alloca returns [LLVMParseInstruction instr]
    :   init_identifier ASSIGN ALLOCA
        type_with_pointer_and_function // TODO: is void allowed?
        (COMMA overall_type literal)? // number should be positive
        (COMMA alignment )?
        (COMMA EXCLAMATION DEBUG debug_line)?
        {
            $instr = new LLVMParseInstruction(LLVMInstructionType.ALLOCA);
            instr.addParam($init_identifier.literal);
            instr.addParam($type_with_pointer_and_function.type);
            
            if($overall_type.type != null) {
                instr.addParam(true);
                instr.addParam($overall_type.type);
                instr.addParam($literal.literal);
            } else {
                instr.addParam(false);
            }
            
            if($alignment.literal != null) {
                instr.addParam(true);
                instr.addParam($alignment.literal);
            } else {
                instr.addParam(false);
            }
            
            instr.addParam($debug_line.literal);
        }
    ;

instruction_binary returns [LLVMParseInstruction instr] // binary instructions for integeres like multiplication, substraction or summation
@init {
    $instr = new LLVMParseInstruction(LLVMInstructionType.BINARY);
    LLVMBinaryOpType binOpType = null;
    Boolean nuw = false;
    Boolean nsw = false; 
    Boolean exact = false;
}
    : init_identifier
      ASSIGN
        ( ADD {binOpType = LLVMBinaryOpType.ADD;}
        | SUB {binOpType = LLVMBinaryOpType.SUB;}
        | MUL {binOpType = LLVMBinaryOpType.MUL;}
        | UDIV {binOpType = LLVMBinaryOpType.UDIV;}
        | SDIV {binOpType = LLVMBinaryOpType.SDIV;}
        | UREM {binOpType = LLVMBinaryOpType.UREM;}
        | SREM {binOpType = LLVMBinaryOpType.SREM;}
        | SHL {binOpType = LLVMBinaryOpType.SHL;}
        | LSHR {binOpType = LLVMBinaryOpType.LSHR;}
        | ASHR {binOpType = LLVMBinaryOpType.ASHR;}
        | AND {binOpType = LLVMBinaryOpType.AND;}
        | OR {binOpType = LLVMBinaryOpType.OR;}
        | XOR {binOpType = LLVMBinaryOpType.XOR;}
        | FADD {binOpType = LLVMBinaryOpType.FADD;}
        | FSUB {binOpType = LLVMBinaryOpType.FSUB;}
        | FMUL {binOpType = LLVMBinaryOpType.FMUL;}
        | FDIV {binOpType = LLVMBinaryOpType.FDIV;}
        | FREM {binOpType = LLVMBinaryOpType.FREM;}
        )
        (EXACT {exact = true;})?
        (NUW {nuw = true;})?
        (NSW {nsw = true;})?
        overall_type  
        l1 = literal  COMMA // first argument
        l2 = literal     // second argument
        (COMMA EXCLAMATION DEBUG debug_line)?
        {
          $instr.addParam($init_identifier.literal);
            $instr.addParam(binOpType);
            // check if exact is used correctly, exact can only be used with udiv, sdiv, lshr, ashr
            if(Globals.useAssertions) {
              if(exact) {
                assert(LLVMParseInstruction.isBinaryOpExactCompatible(binOpType));
              }
            } 
            $instr.addParam(exact);  
            $instr.addParam(nuw);
            $instr.addParam(nsw);
            $instr.addParam($overall_type.type);
            $instr.addParam($l1.literal);
            $instr.addParam($l2.literal);
            $instr.addParam($debug_line.literal);
        }
    ;

instruction_br returns [LLVMParseInstruction instr]
    :   BR
        (
          overall_type literal COMMA // condition type and condition value
          l1=label_type id1=identifier COMMA
          l2=label_type id2=identifier // TODO: change to java request with INTERGER_TYPE
          (COMMA EXCLAMATION DEBUG d1=debug_line)?
          (COMMA EXCLAMATION DEBUG_IDENTIFIER EXCLAMATION INT_NUMBER)?
            {
                // conditional branch
                instr = new LLVMParseInstruction(LLVMInstructionType.COND_BR);
                instr.addParam($overall_type.type); // condition type
                instr.addParam($literal.literal); // condition
                instr.addParam($l1.type); // ifTrueType 
                instr.addParam($id1.literal); // ifTrueAddress
                instr.addParam($l2.type); // ifFalseType
                instr.addParam($id2.literal); // ifFalseAddress
                instr.addParam($d1.literal);
            }
        |
            l1=label_type id1=identifier
            (COMMA EXCLAMATION DEBUG d2=debug_line)?
            (COMMA EXCLAMATION DEBUG_IDENTIFIER EXCLAMATION INT_NUMBER)?
            { 
              // unconditional branch
              instr = new LLVMParseInstruction(LLVMInstructionType.UNCOND_BR);          
                instr.addParam($l1.type); // destination type
                instr.addParam($id1.literal); // destination name 
                instr.addParam($d2.literal);
            }
        )
    ;   

instruction_call returns [LLVMParseInstruction instr]
@init{
    instr = new LLVMParseInstruction(LLVMInstructionType.CALL);
    Boolean tail = false;
    Boolean sig = false;
    ArrayList<Object> funcAttr = new ArrayList<Object>();
    ArrayList<Object> funcParams = new ArrayList<Object>();
    ArrayList<Object> retParams = new ArrayList<Object>();
    ArrayList<Object> sigParams = new ArrayList<Object>();
    ArrayList<String> metaRefs = new ArrayList<String>();
}
    :   (id1=init_identifier ASSIGN )? // no assignment needed for functions which have void as return type
        (TAIL {tail = true;})?
        CALL
        calling_convention?
        (parameter_attribute {retParams.add($parameter_attribute.attribute);})* // return parameters
        (
                 f1=type_with_pointer
                 |
                 f1=void_type
        ) // return type
        (
          OPENP
          (
            (
              f4=overall_type {sigParams.add($f4.type);}
              (COMMA f5=overall_type {sigParams.add($f5.type);})*
              (COMMA DOTS {sigParams.add(null);})?
            ) | DOTS  {sigParams.add(null);}
          )
          CLOSEP STAR?
          {sig = true;}
        )?  // signature is optional
        (
            id2=identifier // function name
        |   id2=constant_expression
        )
        OPENP
        (
            METADATA?
            (
              (
                EXCLAMATION (md1=INT_NUMBER {metaRefs.add($md1.text);} | DIEXPRESSION)
              )
            | (
                f2=full_type_r_no_metadata {funcParams.add($f2.param);}
                alignment?
                l2=literal {funcParams.add($l2.literal);}
              )
            )
            (
                COMMA
                METADATA?
                (
                  (
                    EXCLAMATION (md2=INT_NUMBER {metaRefs.add($md2.text);} | DIEXPRESSION)
                  )
                | (
                    f3=full_type_r_no_metadata
                    {funcParams.add($f3.param);}
                    alignment?
                    l3=literal
                    {funcParams.add($l3.literal);}
                  )
                )
            )*
        )?
        CLOSEP
        (HASH INT_NUMBER)*
        (COMMA EXCLAMATION DEBUG debug_line)?
        (
            function_attribute {funcAttr.add($function_attribute.attribute);}
        )* 
        {
            if(id1 != null) {
                instr.addParam(true);
                instr.addParam($id1.literal);
            } else {
                instr.addParam(false);
            }
            instr.addParam(tail);

            if($calling_convention.callConv != null) {
                instr.addParam(true);
                instr.addParam($calling_convention.callConv);
            } else {
                instr.addParam(false);
            }           

            instr.addParam(retParams.size());
            for(Object elem : retParams) {
                instr.addParam(elem);
            }

            instr.addParam($f1.type); // return type

            instr.addParam(sig); // signature
            if (sig) {
                instr.addParam(sigParams.size());
                for(Object elem : sigParams) {
                    instr.addParam(elem);
                }
            }

            instr.addParam($id2.literal); // function name

            instr.addParam(funcParams.size());
            for(Object elem : funcParams) {
                instr.addParam(elem);
            }

            instr.addParam(funcAttr.size());
            for(Object attr : funcAttr) {
                instr.addParam(attr);
            }

            instr.addParam($debug_line.literal);

            // Detect debug intrinsics (llvm.dbg.declare / llvm.dbg.value / ...). These are not analyzed but
            // for llvm.dbg.declare we remember the binding "pointer of an alloca -> DILocalVariable" so that the
            // source-level signedness of the variable can later be recovered from the debug metadata. Note that the
            // leading "@" of the function name has already been stripped by the identifier rule.
            String dbgFuncName = ($id2.literal instanceof LLVMParseVariableLiteral)
                ? ((LLVMParseVariableLiteral)$id2.literal).getName() : null;
            if (dbgFuncName != null && dbgFuncName.startsWith("llvm.dbg.")) {
                instr.setDbgIntrinsic(true);
                if (dbgFuncName.startsWith("llvm.dbg.declare")
                    && funcParams.size() >= 2 && !metaRefs.isEmpty()
                    && (funcParams.get(1) instanceof LLVMParseLiteral)) {
                    instr.setDbgDeclare((LLVMParseLiteral)funcParams.get(1), Integer.parseInt(metaRefs.get(0)));
                }
            }
        }
    ;

instruction_cmp_int returns [LLVMParseInstruction instr]
@init{
    $instr = new LLVMParseInstruction(LLVMInstructionType.INT_CMP);
    LLVMIntCmpOpType intCmpInstrType = null;
} 
    :   init_identifier ASSIGN
        ICMP
        ( EQ  {intCmpInstrType=LLVMIntCmpOpType.EQ;}
        | NE  {intCmpInstrType=LLVMIntCmpOpType.NE;}
        | UGT {intCmpInstrType=LLVMIntCmpOpType.UGT;}
        | UGE {intCmpInstrType=LLVMIntCmpOpType.UGE;}
        | ULT {intCmpInstrType=LLVMIntCmpOpType.ULT;}
        | ULE {intCmpInstrType=LLVMIntCmpOpType.ULE;}
        | SGT {intCmpInstrType=LLVMIntCmpOpType.SGT;}
        | SGE {intCmpInstrType=LLVMIntCmpOpType.SGE;}
        | SLT {intCmpInstrType=LLVMIntCmpOpType.SLT;}
        | SLE {intCmpInstrType=LLVMIntCmpOpType.SLE;}
        )
        overall_type 
        l1=literal COMMA
        l2=literal
        (COMMA EXCLAMATION DEBUG debug_line)?
        {
            instr.addParam($init_identifier.literal);
            instr.addParam(intCmpInstrType);
            instr.addParam($overall_type.type);
            instr.addParam($l1.literal);
            instr.addParam($l2.literal);
            instr.addParam($debug_line.literal);
        }
    ;
    
instruction_cmp_float returns [LLVMParseInstruction instr]
@init{
    $instr = new LLVMParseInstruction(LLVMInstructionType.FLOAT_CMP);
    LLVMFloatCmpOpType floatCmpInstrType = null;
} 
    : init_identifier
      ASSIGN
        FCMP
        (
          FALSE {floatCmpInstrType=LLVMFloatCmpOpType.FALSE;}
        | OEQ {floatCmpInstrType=LLVMFloatCmpOpType.OEQ;}
        | OGT {floatCmpInstrType=LLVMFloatCmpOpType.OGT;}
        | OGE {floatCmpInstrType=LLVMFloatCmpOpType.OGE;}
        | OLT {floatCmpInstrType=LLVMFloatCmpOpType.OLT;}
        | OLE {floatCmpInstrType=LLVMFloatCmpOpType.OLE;}
        | ONE {floatCmpInstrType=LLVMFloatCmpOpType.ONE;}
        | ORD {floatCmpInstrType=LLVMFloatCmpOpType.ORD;}
        | UEQ {floatCmpInstrType=LLVMFloatCmpOpType.UEQ;}
        | UGT {floatCmpInstrType=LLVMFloatCmpOpType.UGT;}
        | UGE {floatCmpInstrType=LLVMFloatCmpOpType.UGE;}
        | ULT {floatCmpInstrType=LLVMFloatCmpOpType.ULT;}
        | ULE {floatCmpInstrType=LLVMFloatCmpOpType.ULE;}
        | UNE {floatCmpInstrType=LLVMFloatCmpOpType.UNE;}
        | UNO {floatCmpInstrType=LLVMFloatCmpOpType.UNO;}
        | TRUE {floatCmpInstrType=LLVMFloatCmpOpType.TRUE;}
        )
        overall_type 
        l1=literal COMMA
        l2=literal
        (COMMA EXCLAMATION DEBUG debug_line)?
        {
            instr.addParam($init_identifier.literal);
            instr.addParam(floatCmpInstrType);
            instr.addParam($overall_type.type);
            instr.addParam($l1.literal);
            instr.addParam($l2.literal);
            instr.addParam($debug_line.literal);
        }
    ;
    
instruction_conversion returns [LLVMParseInstruction instr]
@init{
    $instr = new LLVMParseInstruction(LLVMInstructionType.CONVERSION);
    LLVMConvInstrType convInstrType = null;
}   
    : init_identifier
      ASSIGN
        ( ZEXT {convInstrType=LLVMConvInstrType.ZEXT;}
        | SEXT {convInstrType=LLVMConvInstrType.SEXT;}
        | FPEXT {convInstrType=LLVMConvInstrType.FPEXT;}
        | TRUNC {convInstrType=LLVMConvInstrType.TRUNC;}
        | FPTRUNC {convInstrType=LLVMConvInstrType.FPTRUNC;}
        | FPTOUI {convInstrType=LLVMConvInstrType.FPTOUI;}
        | FPTOSI {convInstrType=LLVMConvInstrType.FPTOSI;}
        | UITOFP {convInstrType=LLVMConvInstrType.UITOFP;}
        | SITOFP {convInstrType=LLVMConvInstrType.SITOFP;}
        | PTRTOINT {convInstrType=LLVMConvInstrType.PTRTOINT;}
        | INTTOPTR {convInstrType=LLVMConvInstrType.INTTOPTR;}
        | BITCAST {convInstrType=LLVMConvInstrType.BITCAST;}
        )
        overall_type
        literal
        TO
        type_with_pointer_and_function
        (COMMA EXCLAMATION DEBUG debug_line)?
        {
            instr.addParam($init_identifier.literal);
            instr.addParam(convInstrType);
            instr.addParam($overall_type.type);
            instr.addParam($literal.literal);
            instr.addParam($type_with_pointer_and_function.type);
            instr.addParam($debug_line.literal);
        }
    ;

instruction_extractelement returns [LLVMParseInstruction instr] // vector operation
@init{
    $instr = new LLVMParseInstruction(LLVMInstructionType.EXTRACTELEMENT);
}   
    :   identifier 
        ASSIGN
        EXTRACTELEMENT
        o1 = overall_type l1 = literal  COMMA
        o2 = overall_type l2 = literal  // TODO: only i32 als integer type possible, get with java
        (COMMA EXCLAMATION DEBUG debug_line)?
        {
            instr.addParam($identifier.literal);
            instr.addParam($o1.type);
            instr.addParam($l1.literal);
            instr.addParam($o2.type);
            instr.addParam($l2.literal);
            instr.addParam($debug_line.literal);
        }
    ;

instruction_extractvalue returns [LLVMParseInstruction instr] //operation for aggregate types
@init{
    $instr = new LLVMParseInstruction(LLVMInstructionType.EXTRACTVALUE);
    ArrayList<LLVMParseLiteral> indices = new ArrayList<LLVMParseLiteral>(); 
}       
    :   init_identifier ASSIGN
        EXTRACTVALUE
        overall_type l1=literal COMMA // aggregate value
        l2=literal {indices.add($l2.literal);} // index which will be accessed
        (COMMA l3=literal {indices.add($l3.literal);})*  // further indices which will be accessed
        (COMMA EXCLAMATION DEBUG debug_line)?
        {
            instr.addParam($init_identifier.literal);
            instr.addParam($overall_type.type);
            instr.addParam($l1.literal);
            instr.addParam(indices.size());
            for(LLVMParseLiteral index: indices) {
                instr.addParam(index);
            }
            instr.addParam($debug_line.literal);
        }
    ;

instruction_getelementptr returns [LLVMParseInstruction instr]
@init{
    $instr = new LLVMParseInstruction(LLVMInstructionType.GETELEMENTPTR);
    Boolean inbounds = false;
    ArrayList<Object> indices = new ArrayList<Object>();
}
    :   init_identifier ASSIGN {instr.addParam($init_identifier.literal);}
        GEP
        (INBOUNDS {inbounds = true;})? {instr.addParam(inbounds);}
        o1=overall_type
        (COMMA o0=overall_type {o1 = o0;})? // pointer type
        l1=literal // pointer value
        {   instr.addParam($o1.type);
            instr.addParam($l1.literal);
        }
        (COMMA
         o2=overall_type // index types
         l2=literal // index values
            {   indices.add($o2.type);
                indices.add($l2.literal);
            }
        )+
        (COMMA EXCLAMATION DEBUG debug_line)?
        {
            instr.addParam(indices.size());
            for(Object index: indices) {
                instr.addParam(index);
            }
            instr.addParam($debug_line.literal);
        }
    ;

instruction_insertelement   returns [LLVMParseInstruction instr] // vector operation
@init{
    $instr = new LLVMParseInstruction(LLVMInstructionType.INSERTELEMENT);
}           
    :   init_identifier ASSIGN
        INSERTELEMENT
        o1=overall_type l1=literal COMMA
        t2=type_with_pointer l2=literal COMMA
        o3=overall_type l3=literal  // TODO: only i32 as integer type possible, get with java
        (COMMA EXCLAMATION DEBUG debug_line)?
        {
            instr.addParam($init_identifier.literal);
            instr.addParam($o1.type);
            instr.addParam($l1.literal);
            instr.addParam($t2.type);
            instr.addParam($l2.literal);
            instr.addParam($o3.type);
            instr.addParam($l3.literal);
            instr.addParam($debug_line.literal);
        }
    ;
    
instruction_insertvalue returns [LLVMParseInstruction instr]//operation for aggregate types
@init{
        instr = new LLVMParseInstruction(LLVMInstructionType.INSERTVALUE);
        ArrayList<Object> indices = new ArrayList<Object>();
}
        :   
        init_identifier ASSIGN
        INSERTVALUE
        o1=overall_type l1=literal COMMA // array or vector which will be updated
        o2=overall_type l2=literal COMMA // element which will be inserted
        l3=literal  {indices.add($l3.literal);} // index
        (COMMA l4=literal {indices.add($l4.literal);})*  // further index values like in getelementptr
        (COMMA EXCLAMATION DEBUG debug_line)?
        {
            instr.addParam($init_identifier.literal);
            instr.addParam($o1.type);
            instr.addParam($l1.literal);
            instr.addParam($o2.type);
            instr.addParam($l2.literal);
            instr.addParam(indices.size());
            for (Object index : indices) { //indices
                instr.addParam(index);
            }
            instr.addParam($debug_line.literal);
        }
    ;   
    
instruction_indirect_br returns [LLVMParseInstruction instr]
@init{
    instr = new LLVMParseInstruction(LLVMInstructionType.INDIRECT_BR);
    ArrayList<Object> labels = new ArrayList<Object>();
}
    :   INDIRECTBR
        (
            overall_type literal COMMA // address of the label to jump to
            OPENB
               l1=label_type id1=identifier // first possible label
               {
                    labels.add($l1.type);
                    labels.add($id1.literal);
               }
               (
                    COMMA l2=label_type id2=identifier // further possible labels
                    {
                        labels.add($l2.type);
                        labels.add($id2.literal);                   
                    }
               )*
            CLOSEB
        )
        (COMMA EXCLAMATION DEBUG debug_line)?
        {
            instr.addParam($overall_type.type); // address type
            instr.addParam($literal.literal); // address
            instr.addParam(labels.size()); 
            for (Object label : labels) { // possible labels
                instr.addParam(label);
            }
            instr.addParam($debug_line.literal);
        }
    ;

instruction_invoke returns [LLVMParseInstruction instr]
@init{
        instr = new LLVMParseInstruction(LLVMInstructionType.INVOKE);
        ArrayList<Object> funcAttr = new ArrayList<Object>();
        ArrayList<Object> funcParams = new ArrayList<Object>();
}   
    :
        (id1=init_identifier ASSIGN)?
        INVOKE
        calling_convention?
        f1=full_type_n // return type
        id2=identifier  // function name
        OPENP (
                 f2=full_type_r {funcParams.add($f2.param);} 
                 l2=literal {funcParams.add($l2.literal);}
                 (COMMA f3=full_type_r {funcParams.add($f3.param);}
                            l3=literal {funcParams.add($l3.literal);}
                 )*
         )? CLOSEP
        (HASH INT_NUMBER)*
        (COMMA EXCLAMATION DEBUG debug_line)?
        (
            function_attribute {funcAttr.add($function_attribute.attribute);}
        )* 
        TO label_type normalLabel=identifier // normal label
        UNWIND label_type exceptionLabel=identifier // exception label
        {
            // no assignment needed for functions which have void as return type
            if(id1 != null) {
                instr.addParam(true);
                instr.addParam($id1.literal);
            } else {
                instr.addParam(false);
            }
            
            // calling convention
            if($calling_convention.callConv != null) {
                instr.addParam(true);
                instr.addParam($calling_convention.callConv);
            } else {
                instr.addParam(false);
            }           
            
            instr.addParam($f1.returnParam); // return type
            instr.addParam($id2.literal); // function name
            
            // function parameters
            instr.addParam(funcParams.size());
            for(Object elem : funcParams) {
                instr.addParam(elem);
            }
            
            // function attributes
            instr.addParam(funcAttr.size()); 
            for(Object attr : funcAttr) {
                instr.addParam(attr);
            }
            
            // normal label
            instr.addParam($normalLabel.literal);
            // exception label
            instr.addParam($exceptionLabel.literal);
            
            instr.addParam($debug_line.literal);
        }        
    ;
    
instruction_load returns [LLVMParseInstruction instr]
@init{
        instr = new LLVMParseInstruction(LLVMInstructionType.LOAD);
        Boolean isVolatile = false;
        Boolean alignment = false;
}   
    :   init_identifier ASSIGN
        LOAD
        (VOLATILE {isVolatile = true;})?
        o1=overall_type
        (COMMA o2=overall_type {o1 = o2;})?
        literal
        (COMMA alignment {alignment = true;})? // TODO: add !nontemporal
        (COMMA EXCLAMATION DEBUG debug_line)?
        {
            instr.addParam($init_identifier.literal);
            instr.addParam(isVolatile);
            instr.addParam($o1.type);
            instr.addParam($literal.literal);
            instr.addParam(alignment);
            if (alignment) {
                instr.addParam($alignment.literal);
            }
            instr.addParam($debug_line.literal);
        }
    ;

instruction_phi returns [LLVMParseInstruction instr]
@init{
        instr = new LLVMParseInstruction(LLVMInstructionType.PHI);
        ArrayList<Object> args = new ArrayList<Object>();
}   
    :   i1=init_identifier ASSIGN PHI
        o1=overall_type
        OPENB l2=literal COMMA  i2=identifier  CLOSEB// first argument pair
        (COMMA OPENB  l3=literal COMMA  i3=identifier CLOSEB // further argument pairs
            { args.add($l3.literal);
                args.add($i3.literal);                  
            }
        )*  
        (COMMA EXCLAMATION DEBUG debug_line)?
        {
            instr.addParam($i1.literal); // identifier
            instr.addParam($o1.type);
            instr.addParam(args.size()+2); // +2 because of first argument pair
            instr.addParam($l2.literal); // first argument pair
            instr.addParam($i2.literal); 
            for(Object arg:args) { // further argument pairs
                instr.addParam(arg);
            }
            instr.addParam($debug_line.literal);
        }
    ;

instruction_ret returns [LLVMParseInstruction instr] // TODO: type problem
@init{
        instr = new LLVMParseInstruction(LLVMInstructionType.RET);
}   
    :   RET (
                 type_with_pointer_and_function literal
                 |
                 void_type
              ) 
        (COMMA EXCLAMATION DEBUG debug_line)?
        {
            if($type_with_pointer_and_function.type != null) {
                instr.addParam(true);
                instr.addParam($type_with_pointer_and_function.type);
                instr.addParam($literal.literal);
            } else {
                instr.addParam(false);
                instr.addParam($void_type.type);
            }
            instr.addParam($debug_line.literal);
        }
    ;

instruction_select returns [LLVMParseInstruction instr]
@init{
        instr = new LLVMParseInstruction(LLVMInstructionType.SELECT);
}       
    :   init_identifier ASSIGN SELECT
        o1=overall_type  // condition type
        l1=literal COMMA // condition literal
        o2=overall_type l2=literal COMMA // first value
        o3=overall_type l3=literal // second value
        (COMMA EXCLAMATION DEBUG debug_line)?
        {
            instr.addParam($init_identifier.literal);
            instr.addParam($o1.type); // condition type
            instr.addParam($l1.literal); // condition literal
            instr.addParam($o2.type); // first value type
            instr.addParam($l2.literal); // first value
            instr.addParam($o3.type); // second value type
            instr.addParam($l3.literal); // second value
            instr.addParam($debug_line.literal);
        }   
    ;   


instruction_store returns [LLVMParseInstruction instr]
@init{
        instr = new LLVMParseInstruction(LLVMInstructionType.STORE);
        Boolean alignment = false;
        Boolean isVolatile = false;
}       
    :   (VOLATILE {isVolatile = true;})?
      STORE
        o1=overall_type l1=literal //  value to store // TODO: is void allowed?
        COMMA o2=overall_type  l2=literal // address at which to store
        (COMMA alignment {alignment=true;})? // TODO: add !nontemporal
        (COMMA EXCLAMATION DEBUG debug_line)?
        {
          instr.addParam(isVolatile);
            instr.addParam($o1.type);
            instr.addParam($l1.literal);
            instr.addParam($o2.type);
            instr.addParam($l2.literal);
            instr.addParam(alignment);          
            if(alignment) {
                instr.addParam($alignment.literal);
            }
            instr.addParam($debug_line.literal);
        }
    ;
    
instruction_shufflevector   returns [LLVMParseInstruction instr]// vector operation
@init{
        instr = new LLVMParseInstruction(LLVMInstructionType.SHUFFLEVECTOR);
}       
    :   init_identifier ASSIGN
        SHUFFLEVECTOR
        o1=overall_type l1=literal COMMA //first vector argument
        o2=overall_type l2=literal COMMA    // second vector
        o3=overall_type l3=literal  // vector type should be vector of i32 with integer or undef values
        (COMMA EXCLAMATION DEBUG debug_line)?
        {
            instr.addParam($init_identifier.literal);
            instr.addParam($o1.type);
            instr.addParam($l1.literal);
            instr.addParam($o2.type);
            instr.addParam($l2.literal);            
            instr.addParam($o3.type);
            instr.addParam($l3.literal);
            instr.addParam($debug_line.literal);
        }
    ;

    
instruction_switch returns [LLVMParseInstruction instr]
@init{
        instr = new LLVMParseInstruction(LLVMInstructionType.SWITCH);
        ArrayList<Object> jumps = new ArrayList<Object>();
}   // TODO: check if  first Identfier is of type integer and that the other types fit
    : SWITCH
        o1=overall_type l1=literal COMMA
        l2=label_type i2=identifier 
        OPENB
        (
            o3=overall_type l3=literal COMMA l4=label_type i4=identifier
            {
                jumps.add($o3.type); jumps.add($l3.literal);  // type and value of jump number
                jumps.add($l4.type); jumps.add($i4.literal); // label to which will be jumped
            }
        )*
        CLOSEB
        (COMMA EXCLAMATION DEBUG debug_line)?
        {
            instr.addParam($o1.type); // compare type
            instr.addParam($l1.literal); // compare value
            instr.addParam($l2.type); // default label type
            instr.addParam($i2.literal); // default jump value
            instr.addParam(jumps.size()); // jumptable
            for(Object jump:jumps) {
                instr.addParam(jump);
            }
            instr.addParam($debug_line.literal);
        }
    ;    
    
instruction_unreachable returns [LLVMParseInstruction instr]
@init{
        instr = new LLVMParseInstruction(LLVMInstructionType.UNREACHABLE);
}
    : UNREACHABLE
        (COMMA EXCLAMATION DEBUG debug_line)?
    ;
    
instruction_unwind returns [LLVMParseInstruction instr]
@init{
        instr = new LLVMParseInstruction(LLVMInstructionType.UNWIND);
}
    : UNWIND
        (COMMA EXCLAMATION DEBUG debug_line)?
    ;
        
instruction_vaarg returns [LLVMParseInstruction instr]
@init{
        instr = new LLVMParseInstruction(LLVMInstructionType.VAARG);
}
    :   init_identifier ASSIGN VAARG
        o1=overall_type // type of variable argument list 
        l1=literal COMMA // variable argument list
        o2=overall_type // argument type which will be returned
        (COMMA EXCLAMATION DEBUG debug_line)?
        {
            instr.addParam($init_identifier.literal);
            instr.addParam($o1.type);
            instr.addParam($l1.literal);
            instr.addParam($o2.type);
            instr.addParam($debug_line.literal);
        }
    ;   

/** Constant expressions **/

constant_expression returns [LLVMParseLiteral literal]
    :   constant_exp_binary {$literal = $constant_exp_binary.literal;}
    |   constant_exp_conversion {$literal = $constant_exp_conversion.literal;}
    |   constant_exp_extractelement {$literal = $constant_exp_extractelement.literal;}
    |   constant_exp_extractvalue {$literal = $constant_exp_extractvalue.literal;}
    |   constant_exp_fcmp {$literal = $constant_exp_fcmp.literal;}
    |   constant_exp_getelemptr {$literal = $constant_exp_getelemptr.literal;}
    |   constant_exp_icmp {$literal = $constant_exp_icmp.literal;}
    |   constant_exp_insertelement {$literal = $constant_exp_insertelement.literal;}
    |   constant_exp_insertvalue {$literal = $constant_exp_insertvalue.literal;}
    | constant_exp_select {$literal = $constant_exp_select.literal;}
    |   constant_exp_shuffle_vector {$literal = $constant_exp_shuffle_vector.literal;}
    | constant_exp_vaarg {$literal = $constant_exp_vaarg.literal;}
    ;

constant_exp_binary returns [LLVMParseLiteral literal]
@init {
    LLVMParseConstExpression constExp;
    LLVMBinaryOpType op = null; // operation type
    Boolean nuw = false; 
    Boolean nsw = false;
    Boolean exact = false; 
}
    :   ( ADD {op=LLVMBinaryOpType.ADD;}
        | SUB {op=LLVMBinaryOpType.SUB;}
        | MUL {op=LLVMBinaryOpType.MUL;}
        | FADD {op=LLVMBinaryOpType.FADD;}
        | FSUB {op=LLVMBinaryOpType.FSUB;}
        | FMUL {op=LLVMBinaryOpType.FMUL;}
        | FDIV {op=LLVMBinaryOpType.FDIV;}
        | FREM {op=LLVMBinaryOpType.FREM;}
        | UDIV {op=LLVMBinaryOpType.UDIV;}
        | SDIV {op=LLVMBinaryOpType.SDIV;}
        | UREM {op=LLVMBinaryOpType.UREM;}
        | SREM {op=LLVMBinaryOpType.SREM;}
        | SHL {op=LLVMBinaryOpType.SHL;}
        | LSHR {op=LLVMBinaryOpType.LSHR;}
        | ASHR {op=LLVMBinaryOpType.ASHR;}
        | AND {op=LLVMBinaryOpType.AND;}
        | OR {op=LLVMBinaryOpType.OR;}
        | XOR {op=LLVMBinaryOpType.XOR;}
        )
        (EXACT {exact = true;})?
        (NUW {nuw = true;})?
        (NSW {nsw = true;})?
        OPENP
         o1=overall_type  // type
         litL=literal  COMMA // first argument
         overall_type
         litR=literal    // second argument
        CLOSEP
        {
            constExp = new LLVMParseConstExpression(LLVMConstExprType.BINARY);
            constExp.addParam(op); // operation type
            // check if exact is used correctly, exact can only be used with udiv, sdiv, lshr, ashr
      if(Globals.useAssertions) {
        if(exact) {
          assert(LLVMParseConstExpression.isBinaryOpExactCompatible(op));
        }
      }
      constExp.addParam(exact);
            // nuw and nsw
            constExp.addParam(nuw);
            constExp.addParam(nsw);
            // determine type
            constExp.addParam($o1.type);
            // determine left argument
            constExp.addParam($litL.literal);
            // determine right argument
            constExp.addParam($litR.literal);
            // return value
            $literal = constExp;
        }
    ;

constant_exp_conversion returns [LLVMParseLiteral literal]
@init {
    LLVMParseConstExpression constExp = new LLVMParseConstExpression(LLVMConstExprType.CONVERSION);
    LLVMConvInstrType op = null; // operation type 
}       :   
        ( TRUNC {op=LLVMConvInstrType.TRUNC;}
        | ZEXT {op=LLVMConvInstrType.ZEXT;}
        | SEXT {op=LLVMConvInstrType.SEXT;}
        | FPTRUNC {op=LLVMConvInstrType.FPTRUNC;}
        | FPEXT {op=LLVMConvInstrType.FPEXT;}
        | FPTOUI {op=LLVMConvInstrType.FPTOUI;}
        | FPTOSI {op=LLVMConvInstrType.FPTOSI;}
        | UITOFP {op=LLVMConvInstrType.UITOFP;}
        | SITOFP {op=LLVMConvInstrType.SITOFP;}
        | PTRTOINT {op=LLVMConvInstrType.PTRTOINT;}
        | INTTOPTR {op=LLVMConvInstrType.INTTOPTR;}
        | BITCAST {op=LLVMConvInstrType.BITCAST;}
        )
        OPENP
        t1=overall_type  // from type
        lit=literal         // from literal
        TO
        t2=overall_type // to type
        CLOSEP
        {
            constExp.addParam(op); // used conversion type
            constExp.addParam($t1.type); // from type
            constExp.addParam($lit.literal); // literal
            constExp.addParam($t2.type); // to type
            $literal = constExp;
        }
    ;

constant_exp_extractelement returns [LLVMParseLiteral literal]
    :   EXTRACTELEMENT
        OPENP
        ts=overall_type litS=literal  COMMA  // vector
        te=overall_type litE=literal  // index // TODO: only i32 als integer type possible, get with java
        CLOSEP
        {
            LLVMParseConstExpression constExp = new LLVMParseConstExpression(LLVMConstExprType.EXTRACT_ELEMENT);
            constExp.addParam($ts.type);
            constExp.addParam($litS.literal);
            constExp.addParam($te.type);
            constExp.addParam($litE.literal);
            $literal = constExp;
        }
    ;

constant_exp_extractvalue returns [LLVMParseLiteral literal]
@init {
        LLVMParseConstExpression constExp = new LLVMParseConstExpression(LLVMConstExprType.EXTRACT_VALUE);
        ArrayList<Object> indices = new ArrayList<Object>(); 
}   
    :   EXTRACTVALUE
        OPENP
        overall_type {constExp.addParam($overall_type.type);} //type
        litAggr = literal COMMA {constExp.addParam($litAggr.literal);} // aggregate value
        (
            litFirst = literal  // first index which will be accessed
            { indices.add($litFirst.literal); }
        )
        ( COMMA
            litRest = literal // further indices which will be accessed
                { indices.add($litRest.literal); }
        )*
        CLOSEP
        {
            constExp.addParam(indices.size());
            for(Object index : indices) {
                constExp.addParam(index);
            }
            $literal = constExp;
        }
    ;

constant_exp_fcmp returns [LLVMParseLiteral literal]
@init{
        LLVMParseConstExpression constExp = new LLVMParseConstExpression(LLVMConstExprType.FLOAT_CMP);
        LLVMFloatCmpOpType op = null; // operation type
    }
    : FCMP
        ( TRUE  {op=LLVMFloatCmpOpType.TRUE;}
        | FALSE {op=LLVMFloatCmpOpType.FALSE;}
        | OEQ {op=LLVMFloatCmpOpType.OEQ;}
        | OGT {op=LLVMFloatCmpOpType.OGT;}
        | OGE {op=LLVMFloatCmpOpType.OGE;}
        | OLT {op=LLVMFloatCmpOpType.OLT;}
        | OLE {op=LLVMFloatCmpOpType.OLE;}
        | ONE {op=LLVMFloatCmpOpType.ONE;}
        | ORD {op=LLVMFloatCmpOpType.ORD;}
        | UEQ {op=LLVMFloatCmpOpType.UEQ;}
        | UGT {op=LLVMFloatCmpOpType.UGT;}
        | UGE {op=LLVMFloatCmpOpType.UGE;}
        | ULT {op=LLVMFloatCmpOpType.ULT;}
        | ULE {op=LLVMFloatCmpOpType.ULE;}
        | UNE {op=LLVMFloatCmpOpType.UNE;}
        | UNO {op=LLVMFloatCmpOpType.UNO;}
        )
        OPENP
        overall_type
        litLeft = literal COMMA
        litRight = literal
        CLOSEP
        {
            constExp.addParam(op);
            constExp.addParam($overall_type.type);
            constExp.addParam($litLeft.literal);
            constExp.addParam($litRight.literal);
            $literal = constExp;
        }
    ;

constant_exp_getelemptr returns [LLVMParseLiteral literal]
@init{
        LLVMParseConstExpression constExp = new LLVMParseConstExpression(LLVMConstExprType.GET_ELEMENT_PTR);
        Boolean inbounds = false;
        ArrayList<Object> indices = new ArrayList<Object>();
    }
    :   GEP
        (INBOUNDS {inbounds = true;} )?
        {constExp.addParam(inbounds);}
        OPENP
        typePointer = overall_type
        (COMMA typePointer = overall_type)?
        {constExp.addParam($typePointer.type);}
        litPointer = literal {constExp.addParam($litPointer.literal);}
        (COMMA
            typeIndex = overall_type {indices.add($typeIndex.type);}
            litIndex = literal {indices.add($litIndex.literal);}
        )*
        CLOSEP
        {
            constExp.addParam(indices.size());
            for (Object index : indices) {
                constExp.addParam(index);
            }
            $literal = constExp;
        }
    ;

constant_exp_icmp returns [LLVMParseLiteral literal]
@init{
        LLVMParseConstExpression constExp = new LLVMParseConstExpression(LLVMConstExprType.INT_CMP);
        LLVMIntCmpOpType op = null;
    }
    :   ICMP
        ( EQ {op=LLVMIntCmpOpType.EQ;}
        | NE {op=LLVMIntCmpOpType.NE;}
        | UGT {op=LLVMIntCmpOpType.UGT;}
        | UGE {op=LLVMIntCmpOpType.UGE;}
        | ULT {op=LLVMIntCmpOpType.ULT;}
        | ULE {op=LLVMIntCmpOpType.ULE;}
        | SGT {op=LLVMIntCmpOpType.SGT;}
        | SGE {op=LLVMIntCmpOpType.SGE;}
        | SLT {op=LLVMIntCmpOpType.SLT;}
        | SLE {op=LLVMIntCmpOpType.SLE;}
        )
        OPENP
        overall_type 
        lit1=literal COMMA
        lit2=literal
        CLOSEP
        {
            constExp.addParam(op);
            constExp.addParam($overall_type.type);
            constExp.addParam($lit1.literal);
            constExp.addParam($lit2.literal);
            $literal = constExp;
        }
    ;
        
constant_exp_insertelement returns [LLVMParseLiteral literal]
@init{
        LLVMParseConstExpression constExp = new LLVMParseConstExpression(LLVMConstExprType.INSERT_ELEMENT);
    }
    :   INSERTELEMENT
        OPENP
        type1=overall_type  lit1=literal COMMA  // vector
        type2=type_with_pointer lit2=literal COMMA // element which will be inserted
        type3=overall_type lit3=literal  // index // TODO: only i32 als integer type possible, get with java
        CLOSEP
        {
            constExp.addParam($type1.type);
            constExp.addParam($lit1.literal);
            constExp.addParam($type2.type);
            constExp.addParam($lit2.literal);
            constExp.addParam($type3.type);
            constExp.addParam($lit3.literal);
            $literal = constExp;
        }
    ;   

constant_exp_insertvalue returns [LLVMParseLiteral literal]
@init{
        LLVMParseConstExpression constExp = new LLVMParseConstExpression(LLVMConstExprType.INSERT_VALUE);
        ArrayList<Object> indices = new ArrayList<Object>();
    }
    :   INSERTVALUE
        OPENP
        // array or vector which will be updated
        typeComplex = overall_type {constExp.addParam($typeComplex.type);} 
        litComplex = literal COMMA {constExp.addParam($litComplex.literal);}
        
        // element which will be inserted
        typeElem = overall_type {constExp.addParam($typeElem.type);}    
        litElem = literal COMMA {constExp.addParam($litElem.literal);}
         
        // first index with type
        firstIndexType = overall_type {indices.add($firstIndexType.type);}
        firstIndexLit = literal {indices.add($firstIndexLit.literal);}
        // further indices (for indicating deeper elements, e.g. an array in a structure)
        (COMMA
                restindicesType = overall_type {indices.add($restindicesType.type);}    
                restindicesLit = literal {indices.add($restindicesLit.literal);}
            )*  // further indices which will be accessed   
        CLOSEP
        {
            constExp.addParam(indices.size());
            for(Object index : indices) {
                constExp.addParam(index);
            }
            $literal = constExp;
        }   
    ;
    
constant_exp_select returns [LLVMParseLiteral literal]
@init{
        LLVMParseConstExpression constExp = new LLVMParseConstExpression(LLVMConstExprType.SELECT);
    }
    :   SELECT
        OPENP
        o1=overall_type  // condition type
        l1=literal COMMA // condition literal
        o2=overall_type l2=literal COMMA // first value
        o3=overall_type l3=literal // second value  
        CLOSEP
        { 
            constExp.addParam($o1.type);
            constExp.addParam($l1.literal);
            
            constExp.addParam($o2.type);
            constExp.addParam($l2.literal);
            
            constExp.addParam($o3.type);
            constExp.addParam($l3.literal);
            $literal = constExp;
        }
    ;   
    
    
constant_exp_shuffle_vector returns [LLVMParseLiteral literal]
@init{
        LLVMParseConstExpression constExp = new LLVMParseConstExpression(LLVMConstExprType.SHUFFLE_VECTOR);
    }
    :   SHUFFLEVECTOR
        OPENP
         typeL = overall_type (litL=literal) COMMA //first vector argument
         typeR = overall_type (litR=literal) COMMA // second vector
         typeS = overall_type (litS=literal)  // index mask // vector type should be vector of i32 with integer or undef values 
        CLOSEP
        { 
            constExp.addParam($typeL.type);
            constExp.addParam($litL.literal);
            
            constExp.addParam($typeR.type);
            constExp.addParam($litR.literal);
            
            constExp.addParam($typeS.type);
            constExp.addParam($litS.literal);
            $literal = constExp;
        }
    ;
    
constant_exp_vaarg returns [LLVMParseLiteral literal]
@init{
    LLVMParseConstExpression constExp = new LLVMParseConstExpression(LLVMConstExprType.VAARG);
}
    :   VAARG
        OPENP
        o1=overall_type // type of variable argument list 
        l1=literal COMMA // variable argument list
        o2=overall_type // argument type which will be returned
        CLOSEP
        {
            constExp.addParam($o1.type);
            constExp.addParam($l1.literal);
            constExp.addParam($o2.type);
            $literal = constExp;            
        }
    ;

float_type returns [LLVMParseType type]// floating point type
  : FLOAT {$type = new LLVMParseFloatType();}
  | DOUBLE {$type = new LLVMParseDoubleType();}
  | X86_FP80 {$type = new LLVMParseX86_FP80Type();} 
  | FP128  {$type = new LLVMParseFP128Type();}
  | PPC_FP128 {$type = new LLVMParsePPC_FP128Type();}
  ;

label_type returns [LLVMParseLabelType type = new LLVMParseLabelType();]
  : LABEL;


local_identifier returns [LLVMParseType type] //used for type names
    :   LOCAL_IDENTIFIER
        {
            int length = $LOCAL_IDENTIFIER.text.length();
            $type = new LLVMParseNamedType($LOCAL_IDENTIFIER.text.substring(1,length-1));
        }
    ;

int_type returns [LLVMParseIntType type]
  : INT_TYPE
  {  
    int size = Integer.parseInt($INT_TYPE.text.substring(1));
    if(size <= 64 && size >= 0) {
      $type = new LLVMParseIntType(size);
    } 
  }
  // TODO: number <=2^23-1; throw error if size >= 64
  ;

metadata_type returns [LLVMParseMetadataType type = new LLVMParseMetadataType();]
  : METADATA
  ;

void_type returns [LLVMParseType type = new LLVMParseVoidType();]
  : VOID
  ;


/* Literals */

int_literal returns [LLVMParseLiteral literal]
  : INT_NUMBER {$literal = new LLVMParseIntRep($INT_NUMBER.text);}
  | NEGATIVE_INT_NUMBER {$literal = new LLVMParseIntRep($NEGATIVE_INT_NUMBER.text);}
  | TRUE {$literal = new LLVMParseIntRep("1");}
  | FALSE {$literal = new LLVMParseIntRep("0");}
  ;
 
 string_literal returns [LLVMParseLiteral literal]
 :  
        STRING_LITERAL {
            // removing quotation signs
            $literal = new LLVMParseStringLiteral($STRING_LITERAL.text.substring(1,$STRING_LITERAL.text.length()-1));
        }
 ;
 
special_string_literal returns [LLVMParseLiteral literal] 
    : SPECIAL_STRING_LITERAL
        {
            // removing leading 'c' and quotation signs
            $literal = new LLVMParseStringLiteral($SPECIAL_STRING_LITERAL.text.substring(2,$SPECIAL_STRING_LITERAL.text.length()-1));
        }
    ; 
    
fp_literal returns [LLVMParseLiteral literal] 
    :   FLOAT_LITERAL {$literal = new LLVMParseFPNormalRep($FLOAT_LITERAL.text);}
    |   FP_NORMAL_HEX_NUMBER {$literal = new LLVMParseFPHexRep($FP_NORMAL_HEX_NUMBER.text.substring(2), LLVMParseHexFormat.NORMAL);}
    | FP_X86_HEX_NUMBER {$literal = new LLVMParseFPHexRep($FP_X86_HEX_NUMBER.text.substring(3), LLVMParseHexFormat.X86);}
    | FP_PPC_HEX_NUMBER {$literal = new LLVMParseFPHexRep($FP_PPC_HEX_NUMBER.text.substring(3), LLVMParseHexFormat.PPC);}
    | FP_128_HEX_NUMBER {$literal = new LLVMParseFPHexRep($FP_128_HEX_NUMBER.text.substring(3), LLVMParseHexFormat.BIT128);}
    ;

undef_literal returns [LLVMParseLiteral literal = new LLVMParseUndefLiteral();]
    : UNDEF
    ;


/************** Lexer rules **************/

/* key words */
ADD : 'add';
ADDRESSSAFETY : 'address_safety';
ADDRSPACE : 'addrspace';
ALIAS : 'alias';
ALIGN : 'align';
ALIGNSTACK : 'alignstack';
ALLOCA : 'alloca';
ALLOCSIZE : 'allocsize';
ALWAYSINLINE : 'alwaysinline';
AND : 'and';
APPENDING : 'appending';
ARGMEMONLY: 'argmemonly';
ASHR : 'ashr';
ATTRIBUTES : 'attributes';
AVAILABLEEXTERNALLY : 'available_externally';
BITCAST : 'bitcast';
BR : 'br';
BYVAL : 'byval';
CALL : 'call';
CC10 : 'cc 10';
CC11 : 'cc 11';
CCC : 'ccc';
COLDCC : 'coldcc';
COMMON : 'common';
CONSTANT : 'constant';
DATALAYOUT : 'datalayout';
DEBUG : 'dbg';
DECLARE : 'declare';
DEFAULT : 'default';
DEFINE : 'define';
DIEXPRESSION : 'DIExpression()';
DISTINCT : 'distinct';
DLLEXPORT : 'dllexport';
DLLIMPORT : 'dllimport';
DOTS : '...';
DOUBLE : 'double';
DSO_LOCAL : 'dso_local';
EQ : 'eq';
EXACT : 'exact';
EXTERNAL : 'external';
EXTERNWEAK : 'extern_weak';
EXTRACTELEMENT : 'extractelement';
EXTRACTVALUE : 'extractvalue';
FADD : 'fadd';
FALSE : 'false';
FASTCC : 'fastcc';
FCMP : 'fcmp';
FDIV : 'fdiv';
FLOAT : 'float';
FMUL : 'fmul';
FP128 : 'fp128';
FPEXT : 'fpext';
FPTOSI : 'fptosi';
FPTOUI : 'fptoui';
FPTRUNC : 'fptrunc';
FREM : 'frem';
FSUB : 'fsub';
GC : 'gc';
GEP : 'getelementptr';
GLOBAL : 'global';
HIDDEN : 'hidden';
ICMP : 'icmp';
IMMARG : 'immarg';
INBOUNDS : 'inbounds';
INDIRECTBR : 'indirectbr';
INLINEHINT : 'inlinehint';
INREG : 'inreg';
INSERTELEMENT : 'insertelement';
INSERTVALUE : 'insertvalue';
INTERNAL : 'internal';
INTTOPTR : 'inttoptr';
INVOKE : 'invoke';
LABEL : 'label';
LINKERPRIVATE : 'linker_private';
LINKERPRIVATEWEAK : 'linker_private_weak';
LINKERPRIVATEWEAKDEFAUTO : 'linker_private_weak_def_auto';
LINKONCE : 'linkonce';
LINKONCEODR : 'linkonce_odr';
LOAD : 'load';
LSHR : 'lshr';
METADATA : 'metadata';
MUL : 'mul';
NAKED : 'naked';
NE : 'ne';
NEST : 'nest';
NONNULL: 'nonnull';
NOALIAS : 'noalias';
NOCAPTURE : 'nocapture';
NODUPLICATE : 'noduplicate';
NOIMPLICITFLOAT : 'noimplicitfloat';
NOINLINE : 'noinline';
NOLAZYBIND : 'nolazybind';
NOREDZONE : 'noredzone';
NORETURN : 'noreturn';
NOUNWIND : 'nounwind';
NSW : 'nsw';
NULL : 'null';
NUW : 'nuw';
OEQ : 'oeq';
OGE : 'oge';
OGT : 'ogt';
OLE : 'ole';
OLT : 'olt';
ONE : 'one';
OPTNONE : 'optnone';
OPTSIZE : 'optsize';
OR : 'or';
ORD : 'ord';
PHI : 'phi';
PPC_FP128 : 'ppc_fp128';
PRIVATE : 'private';
PROTECTED : 'protected';
PTRTOINT : 'ptrtoint';
READNONE : 'readnone';
READONLY : 'readonly';
RET : 'ret';
RETURNSTWICE : 'returns_twice';
SDIV : 'sdiv';
SECTION : 'section';
SELECT : 'select';
SEXT : 'sext';
SGE : 'sge';
SGT : 'sgt';
SHL : 'shl';
SHUFFLEVECTOR : 'shufflevector';
SIGNEXT : 'signext';
SITOFP : 'sitofp';
SLE : 'sle';
SLT : 'slt';
SOURCEFILENAME : 'source_filename';
SPECULATABLE : 'speculatable';
SREM : 'srem';
SRET : 'sret';
SSP : 'ssp';
SSPREQ : 'sspreq';
STORE : 'store';
SUB : 'sub';
SWITCH : 'switch';
TAIL : 'tail';
TARGET : 'target';
THREAD_LOCAL : 'thread_local';
TIMES : 'x';
TO : 'to';
TRIPLE : 'triple';
TRUE : 'true';
TRUNC : 'trunc';
TYPE : 'type';
UDIV : 'udiv';
UEQ : 'ueq';
UGE : 'uge';
UGT : 'ugt';
UITOFP : 'uitofp';
ULE : 'ule';
ULT : 'ult';
UNDEF : 'undef';
UNE : 'une';
UNNAMED_ADDR : 'unnamed_addr';
UNO : 'uno';
UNREACHABLE : 'unreachable';
UNWIND : 'unwind';
UREM : 'urem';
UWTABLE : 'uwtable';
VAARG : 'va_arg';
VOID : 'void';
VOLATILE : 'volatile';
WEAK : 'weak';
WEAKODR : 'weak_odr';
WILLRETURN : 'willreturn';
WRITEONLY : 'writeonly';
X86_FP80 : 'x86_fp80';
XOR : 'xor';
ZEROEXT : 'zeroext';
ZEROINITIALIZER : 'zeroinitializer';
ZEXT : 'zext';


/* Primitive types*/
INT_TYPE    // Integer type
    :   'i' INT_NUMBER 
    ; 

NEGATIVE_INT_NUMBER
    :   '-' INT_NUMBER 
    ;  

INT_NUMBER
    :    DIGIT+
    ;
    
STRING_LITERAL
    :
    '"'
    ( ~(  '"' | '\r' | '\n' ))*
    '"'
    ;

SPECIAL_STRING_LITERAL // C programs translated to LLVM have a special syntax for string constants, which will be taken into account with this rule
    :
    'c'
    '"'
    ( ~(  '"' | '\r' | '\n' ))*
    '"'
    ;

fragment CHAR
    :   LOWER_CHAR
    |   UPPER_CHAR
    ;

fragment LOWER_CHAR
    :   'a'..'z'
    ;

fragment UPPER_CHAR
    :   'A'..'Z'
    ;
    
fragment EXTRA_CHAR // some extra characters needed for definition of  identifiers
    :   '$'|'.'|'_'
    ;

FLOAT_LITERAL
    :   NEGATIVE_FLOAT_NUMBER
    |   FLOAT_NUMBER
    ;

fragment NEGATIVE_FLOAT_NUMBER
    :   ('-') FLOAT_NUMBER
    ;

fragment FLOAT_NUMBER
    :   DIGIT+ '.' DIGIT* Exponent?
    |   '.' DIGIT+ Exponent?
    |   DIGIT+ Exponent
    ;

fragment Exponent : ('e'|'E') ('+'|'-')? DIGIT+ ;

FP_NORMAL_HEX_NUMBER
    :   '0x' HexDigit+
    ;
    
FP_X86_HEX_NUMBER
    :   '0xK'HexDigit+ // The 80-bit format used by x86 is represented as 0xK followed by 20 hexadecimal digits
    ;

FP_PPC_HEX_NUMBER
    :   '0xM'HexDigit+ // The 128-bit format used by PowerPC (two adjacent doubles) is represented by 0xM followed by 32 hexadecimal digits.
    ;

FP_128_HEX_NUMBER
    :   '0xL'HexDigit+ // 128-bit format is represented by 0xL followed by 32 hexadecimal digits
    ;
        
fragment HexDigit
    :   (DIGIT|'a'..'f'|'A'..'F')
    ;


/* identifiers */
DEBUG_IDENTIFIER 
    :   (
        (CHAR | EXTRA_CHAR)+
        |
        STRING_LITERAL
        )
    ;

GLOBAL_IDENTIFIER // global identifiers  begin with '@' 
    :   (
        ATSYMBOL  (CHAR | EXTRA_CHAR | DIGIT)+
        |
        ATSYMBOL STRING_LITERAL
        )
    ;

LOCAL_IDENTIFIER // local identifiers begin  with '%' 
    :   (
        PERCENT  (CHAR | EXTRA_CHAR | DIGIT)+
        |
        PERCENT STRING_LITERAL
        )
    ;


/* Ungrouped tokens */
CC_NUMBER : 'cc' DIGIT+; // TODO: 1<= number >=64
fragment DIGIT : '0'..'9';
LINE_COMMENT : ';' ( ~ ('\r\n' | '\r' | '\n'))* ('\r\n' | '\r' | '\n') {$channel=HIDDEN;} ;
WS : ( ' ' | '\r' | '\t' | '\n' | '\r\n' ) {$channel=HIDDEN;} ;
LABEL1 : (CHAR | EXTRA_CHAR | DIGIT)+;
label1_or_int : LABEL1 | INT_NUMBER;
OPENP : '(';
CLOSEP : ')';
STAR : '*';
ASSIGN : '=';
ATSYMBOL : '@';
PERCENT : '%';
COMMA : ',';
OPENC : '{';
CLOSEC : '}';
OPENB : '[';
CLOSEB : ']';
OPENA : '<';
CLOSEA : '>';
COLON : ':';
HASH : '#'; 
EXCLAMATION: '!';
