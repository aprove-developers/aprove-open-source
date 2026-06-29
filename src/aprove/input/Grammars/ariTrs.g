/*   Type:        ANTLR
 *   Title:       PTRS grammar with ARI format
 *   Description: A grammar definiton for TRSs based on the new ARI format
 *   Project:     AProVE
 *   Authors:     Jan-Christoph Kassing
 *   Copyright:   Copyright (c) 2024
 *   Department:  RWTH Aachen / Templergraben 55 / D-52056 Aachen
 */

grammar ariTrs;

options {
    language = Java;
}

@members {
    private boolean isReservedWord(String text) {
        return text.equals("fun") || text.equals("rule") || text.equals("format")
            || text.equals("sort") || text.equals("theory") || text.equals("define-fun")
            || text.equals("prule") || text.equals("->") || text.equals("entrypoint");
    }
}

// replace default error recovery behavior for parser by actually /rejecting/
// unsupported inputs instead of recovering using the follow set
// (alternative fix: override reportError methods as in Strategy.g)
@rulecatch {
catch (RecognitionException e) {
    if (true) {
        // if (true): kludge to persuade the Java compiler that some later
        // (here auto-generated) unreachable return statements might be
        // reachable after all and is thus not to be deemed a compile error
        throw e;
    }
}
}

@header {
package aprove.input.Generated.ariTrs;

import org.apache.commons.math3.fraction.BigFraction;

import aprove.input.Utility.RawAriTrs;
import aprove.input.Utility.UnhandledConstructException;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.input.Utility.*;

import java.util.Set;
import java.util.Map;
import java.util.LinkedHashSet;
import java.util.LinkedHashMap;

}

@lexer::header {
package aprove.input.Generated.ariTrs;
}

trs returns [RawAriTrs rawtrs = new RawAriTrs()]
    : ('(' decl[rawtrs] ')')*
;

decl[RawAriTrs rawtrs]
    : FORMAT formatdecl[rawtrs]
	| FUN functionsymdecl[rawtrs]
    | STRATEGY strategydecl[rawtrs]
    | STARTTERM starttermdecl[rawtrs]
    | GOAL goaldecl[rawtrs]
    | RULE condRule[rawtrs, false]
    | PRULE condPRule[rawtrs, false]
    | INFEASIBLE infeasibleQuery[rawtrs]
    | COMMENT
;

formatdecl [RawAriTrs rawtrs]
	: 'TRS' {rawtrs.setInputFormat(InputFormat.TRS);}
	| 'PTRS' {rawtrs.setInputFormat(InputFormat.PTRS);}
	| 'ETRS' {rawtrs.setInputFormat(InputFormat.ETRS);}
	| 'CTRS' 'oriented' {rawtrs.setInputFormat(InputFormat.CTRS_oriented);}
	| 'CSTRS' {rawtrs.setInputFormat(InputFormat.CSTRS);}
;

functionsymdecl [RawAriTrs rawtrs]
	: id=identifier ar=INTEGER ( THEORY theory_id=identifier )? ( REPLACEMENTS '(' intSet=integerlist ')' )? {
	
        // Handle "|"-Symbols in identifiers
        char first = id.charAt(0);
        char last = id.charAt(id.length() - 1);
        if( first == '|' && last == '|'){
        	id = id.substring(1,id.length() - 1);
        }
		
		FunctionSymbol f = FunctionSymbol.create(id, Integer.parseInt(ar.getText()));
		rawtrs.addFunctionSymbol(f);
		
		if (theory_id != null) {
			switch(theory_id) {
				case "A":
					rawtrs.addAssociativeFunctionSymbol(f);
					break;
				case "C":
					rawtrs.addCommutativeFunctionSymbol(f);
					break;
				case "AC":
					rawtrs.addAssociativeAndCommutativeFunctionSymbol(f);
					break;
				default:
					
			}
		}
		
		if (intSet != null) {
			rawtrs.addReplacementMapEntry(f,intSet);
		}
    }
;

goaldecl [RawAriTrs rawtrs]
    : AST { rawtrs.setAst(true); }
    | PAST { rawtrs.setPast(true); }
    | SAST { rawtrs.setSast(true); }
    | TERMINATION { rawtrs.setTermination(true); }
    | COMPLEXITY { rawtrs.setComplexity(true); }
    | CONFLUENCE { rawtrs.setConfluence(true); }
    | INFEASIBILITY { rawtrs.setInfeasibility(true); }
;

strategydecl [RawAriTrs rawtrs]
    : INNERMOST { rawtrs.setInnermost(); }
    | OUTERMOST { rawtrs.setOutermost(); }
    | PARALLELINNERMOST { rawtrs.setParallelInnermost(true); }
;

starttermdecl [RawAriTrs rawtrs]
    : BASIC { rawtrs.setBasic(true); }
    | ALL { rawtrs.setBasic(false); }
;

condRule[RawAriTrs rawtrs, boolean pairs]
	@init {
        ArrayList<Condition> conds = new ArrayList<Condition>();
    }
    : lhs=term[rawtrs] rhs=term[rawtrs] condlist[rawtrs, conds] ( COST c=INTEGER )? {
    	int cost = 1;
    	if (c != null) {
    		cost = Integer.parseInt(c.getText());
    	}
        rawtrs.addAbstractRule(lhs, rhs, cost == 0, conds);
    }
;

term[RawAriTrs rawtrs] returns [TRSTerm t]
    @after {
        return te;
    }
    : te=constantorvar[rawtrs]
    | te=nonconstant[rawtrs]
;

nonconstant[RawAriTrs rawtrs] returns [TRSTerm t]
    : '(' id=identifier tl=termlist[rawtrs] ')' {
    
    	// Handle "|"-Symbols in identifiers
        char first = id.charAt(0);
        char last = id.charAt(id.length() - 1);
        if( first == '|' && last == '|'){
        	id = id.substring(1,id.length() - 1);
        }
    	
    	int ar = 0;
    	if (tl == null) {
            tl = TRSTerm.EMPTY_ARGS;
        } else {
        	ar = tl.size();
        }
        if (rawtrs.isFunctionSymbol(id, ar)) {
            FunctionSymbol f = FunctionSymbol.create(id, ar);
            return TRSTerm.createFunctionApplication(f, tl);
        } else {
            return TRSTerm.createVariable(id);
        }
    }
;

constantorvar[RawAriTrs rawtrs] returns [TRSTerm t]
	: id=identifier {
	
		// Handle "|"-Symbols in identifiers
        char first = id.charAt(0);
        char last = id.charAt(id.length() - 1);
        if( first == '|' && last == '|'){
        	id = id.substring(1,id.length() - 1);
        }
        
    	int ar = 0;
    	ArrayList<TRSTerm> tl = TRSTerm.EMPTY_ARGS;
        if (rawtrs.isFunctionSymbol(id, ar)) {
            FunctionSymbol f = FunctionSymbol.create(id, ar);
            return TRSTerm.createFunctionApplication(f, tl);
        } else {
            return TRSTerm.createVariable(id);
        }
    }
;

integerlist returns [Set<Integer> ints]
    @init {
        ints = new LinkedHashSet<Integer>();
    }
    : ( num=integer { ints.add(num); } )*
;

termlist[RawAriTrs rawtrs] returns [ArrayList<TRSTerm> terms]
    @init {
        terms = new ArrayList<TRSTerm>();
    }
    : ( t=term[rawtrs] { terms.add(t); } )*
;

infeasibleQuery[RawAriTrs rawtrs]
	@init {
		ArrayList<Condition> queryConds = new ArrayList<Condition>();
	}
	: ( '(' condition[rawtrs, queryConds] ')')+ {
		rawtrs.setInfeasibilityQuery(queryConds);
	}
;

condlist[RawAriTrs rawtrs, ArrayList<Condition> conds]
	: ('(' condition[rawtrs, conds] ')' )*
;

condition[RawAriTrs rawtrs, ArrayList<Condition> conds]
    : '=' lhs=term[rawtrs] rhs=term[rawtrs] { 
    	Condition.ConditionType t = Condition.ConditionType.ARROW;
    	Condition c = Condition.create(lhs, rhs, t); 
    	conds.add(c);
    }
;

condPRule[RawAriTrs rawtrs, boolean pairs]
    : lhs=term[rawtrs] '(' rhs=pruleRhs[rawtrs] ')' {
	    rawtrs.addProbabilisticRule(lhs, rhs);
    }
;

pruleRhs[RawAriTrs rawtrs] returns [MultiDistribution<TRSTerm> termdist]
    @init {
        MultiDistribution.Builder<TRSTerm> distBuilder = new MultiDistribution.Builder<>();
    }
    @after {
        termdist = distBuilder.build();
    }
    : ('(' termProb[rawtrs, distBuilder] ')' )*
;

termProb[RawAriTrs rawtrs, MultiDistribution.Builder<TRSTerm> distBuilder]
	: t=term[rawtrs] ( PROB p=INTEGER )? { 
    	if (p == null) {
    		distBuilder.add(t, 1); 
    	} else {
    		distBuilder.add(t, Integer.parseInt(p.getText())); 
    	}
    }
;

integer returns [int i]
    : intstring=INTEGER { i = Integer.parseInt(intstring.getText()); }
;

// Parser Rule
keyword returns [String kw]
    : tok=(FORMAT | PTRS | FUN | REPLACEMENTS | THEORY | PROB | COST | PRULE | RULE| COMPLEXITY 
    		| AST | PAST | SAST | TERMINATION | GOAL | INNERMOST | OUTERMOST | NOT | RULES 
    		| STRATEGY | VAR | STARTTERM | ALL | BASIC | EQUAL | PARALLELINNERMOST | CONFLUENCE 
    		| INFEASIBILITY | INFEASIBLE)
    { kw = tok.getText(); }
;

strictIdentifier returns [String s]
    : id=SIMPLE_SYMBOL {
        String text = id.getText();
        if (isReservedWord(text)) {
            throw new RuntimeException("Reserved word '" + text + "' cannot be used as identifier.");
        }
        $s = text;
      }
    | id=QUOTED_SYMBOL { $s = id.getText(); }
    | id=INTEGER { $s = id.getText(); }
    ;

identifier returns [String s]
    : kw=keyword { $s = kw; }
    | id=strictIdentifier { $s = $id.s; }
    ;

/* this allows language words to be used as identifiers */
/* see http://www.antlr.org/wiki/pages/viewpage.action?pageId=1741 */
/* if you update this list, also update the keyword rule above */
FORMAT              	: 'format';
PTRS              		: 'PTRS';
FUN              		: 'fun';
REPLACEMENTS			: ':replacement-map';
THEORY              	: ':theory';
PROB              		: ':prob';
COST              		: ':cost';
PRULE              		: 'prule';
RULE 					: 'rule';
COMPLEXITY				: 'COMPLEXITY';
AST              		: 'AST';
PAST        			: 'PAST';
SAST        			: 'SAST';
TERMINATION             : 'TERMINATION';
INNERMOST               : 'INNERMOST';
OUTERMOST               : 'OUTERMOST';
GOAL                    : 'GOAL';
NOT                     : 'NOT';
RULES                   : 'RULES';
STRATEGY                : 'STRATEGY';
VAR                     : 'VAR';
STARTTERM               : 'STARTTERM';
ALL                     : 'ALL';
BASIC                   : 'BASIC';
EQUAL                   : '=';
PARALLELINNERMOST 		: 'PARALLELINNERMOST';
CONFLUENCE				: 'CONFLUENCE';
INFEASIBILITY			: 'INFEASIBILITY';
INFEASIBLE				: 'infeasible?';

// Lexer Rules
SIMPLE_SYMBOL
    : SYMBOL_START SYMBOL_REST*
    ;

fragment SYMBOL_START
    : LETTER | SPECIAL
    ;

fragment SYMBOL_REST
    : LETTER | DIGIT | SPECIAL
    ;

fragment LETTER : 'a'..'z' | 'A'..'Z';
fragment DIGIT  : '0'..'9';
fragment SPECIAL : '~' | '!' | '@' | '$' | '%' | '^' | '&' | '*' | '_' | '-' |
                   '+' | '=' | '<' | '>' | '.' | '?' | '/' | '\'';

QUOTED_SYMBOL
    : '|' QUOTED_CHAR+ '|'
    ;
    
fragment QUOTED_CHAR
    : ~('|' | '\\' | '(' | ')' | ';' | ' ' | '\t' | '\n' | '\r')
    ;
   
INTEGER
    : s=('0'..'9')+
;

WHITESPACE : ( '\t' | ' ' | '\r' | '\n')+ { $channel = HIDDEN; };

COMMENT : ';' ~( '\r' | '\n' )* { $channel = HIDDEN; } ;
