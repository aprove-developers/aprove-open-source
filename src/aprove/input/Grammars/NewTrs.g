/*   Type:        ANTLR
 *   Title:       TRS/QDP/QCSDP grammar
 *   Description: A grammar definiton for TRS programs
 *   Project:     AProVE
 *   Authors:     Fabian Emmes
 *   Copyright:   Copyright (c) 2009
 *   Department:  RWTH Aachen / Templergraben 55 / D-52056 Aachen
 */

grammar NewTrs;

options {
    language = Java;
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
package aprove.input.Generated.newTrs;

import aprove.input.Utility.RawTrs;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

import java.util.Set;
import java.util.Map;
import java.util.LinkedHashSet;
import java.util.LinkedHashMap;

}

@lexer::header {
package aprove.input.Generated.newTrs;
}

trs returns [RawTrs rawtrs = new RawTrs()]
    : ('(' decl[rawtrs] ')')*
;

decl[RawTrs rawtrs]
    : VAR ids=idlist {
        for (String v : ids)
            rawtrs.addVariable(TRSTerm.createVariable(v));
    }
    | THEORY listofthdecl[rawtrs] 
    | RULES rules=listofrules[rawtrs, false] {
        rawtrs.hasRules();
    }
    | STRATEGY strategydecl[rawtrs]
    | PAIRS rules=listofrules[rawtrs, true] {
        rawtrs.hasPairs();
    }
    | EDGES edges=listOfEdges {
        rawtrs.setEdges(edges);
    }
    | Q qterms=listofterms[rawtrs] {
        rawtrs.hasQ();
        for (TRSTerm t : qterms) {
            rawtrs.addQTerm((TRSFunctionApplication) t);
        }
    }
    | MINIMAL {
        rawtrs.setMinimal(true);
    }
    | NOT MINIMAL {
        rawtrs.setMinimal(false);
    }
    | STARTTERM starttermdecl[rawtrs]
    | GOAL goaldecl[rawtrs]
    | IDENTIFIER commentOrIgn
;

goaldecl [RawTrs rawtrs]
    : COMPLEXITY { rawtrs.setComplexity(true); }
    | TERMINATION { rawtrs.setComplexity(false); }
;

starttermdecl [RawTrs rawtrs]
    : CONSTRUCTORBASED { rawtrs.setConstructorbased(true); }
    | UNRESTRICTED { rawtrs.setConstructorbased(false); }
;

strategydecl [RawTrs rawtrs]
    : INNERMOST { rawtrs.setInnermost(true); }
    | OUTERMOST { rawtrs.setOutermost(true); }
    | PARALLELINNERMOST { rawtrs.setParallelInnermost(true); }
    | CONTEXTSENSITIVE csstratlist[rawtrs]
;

// properly nested comments or stuff we don't know. we must parse this :-(
commentOrIgn    : ignored*;
ignored         : identifier
                | STRING
                | ','
                | '->'
                | '->='
                | '-><-'
                | '=='
                | '|'
                | '(' commentOrIgn ')';

listofthdecl[RawTrs rawtrs]
    : ('(' thdecl[rawtrs] ')')*
;

// explicit equations are collected as they are; whether they form a supported
// theory (only A, C, and AC equations so far) is checked by the ObligationCreator
thdecl[RawTrs rawtrs]
    : EQUATIONS eqlist[rawtrs]
    | id=IDENTIFIER ids=idlist {
        String theory = id.getText();
        if ("AC".equals(theory)) {
            for (String i : ids) {
                rawtrs.addAssociativeAndCommutativeName(i);
            }
        } else if ("C".equals(theory)) {
            for (String i : ids) {
                rawtrs.addCommutativeName(i);
            }
        } else if ("A".equals(theory)) {
            for (String i : ids) {
                rawtrs.addAssociativeName(i);
            }
        } else {
            throw new FailedPredicateException(input, "THEORY name", "Unsupported Theory: " + theory + " Currently only theories A, C, AC are supported.");
        }
    }
;

eqlist[RawTrs rawtrs]
    : equation[rawtrs]*
;

equation[RawTrs rawtrs]
    : lhs=term[rawtrs] '==' rhs=term[rawtrs] {
        rawtrs.addEquation(lhs, rhs);
    }
;

listofrules[RawTrs rawtrs, boolean pairs]
    : (condRule[rawtrs, pairs]) *
;

condRule[RawTrs rawtrs, boolean pairs]
    : rtriple=defrule[rawtrs] ('|' conds=condlist[rawtrs])? {
        if (conds == null) {
            conds = ImmutableCreator.create(new ArrayList<Condition>());
        }
        rawtrs.addAbstractRule(rtriple.x, rtriple.y, conds, rtriple.z, pairs);
    }
;

defrule[RawTrs rawtrs] returns [Triple<TRSTerm, TRSTerm, Boolean> r]
    : lhs=term[rawtrs] relative=arrow rhs=term[rawtrs] {
        return new Triple<TRSTerm, TRSTerm, Boolean>(lhs, rhs, relative);
    }
;

arrow returns [Boolean b]
    : '->' { b = false; }
    | '->=' { b = true; }
;

condlist[RawTrs rawtrs] returns [ImmutableList<Condition> conds]
    @init {
        ArrayList<Condition> rawConds = new ArrayList<Condition>();
    }
    :
    c=cond[rawtrs]
        { rawConds.add(c); }
    (','
        c=cond[rawtrs]
        { rawConds.add(c); }
    )*
    {
        conds = ImmutableCreator.create(rawConds);
    }
;

cond[RawTrs rawtrs] returns [Condition c]
    : lhs=term[rawtrs] condtype=condarrow rhs=term[rawtrs]
    { c = Condition.create(lhs, rhs, condtype); }
;

condarrow returns [Condition.ConditionType t]
    : '->'   { t = Condition.ConditionType.ARROW; }
    | '-><-' { t = Condition.ConditionType.JOIN; }
;

listofterms[RawTrs rawtrs] returns [Set<TRSTerm> terms]
    @init {
        terms = new LinkedHashSet<TRSTerm> ();
    }
    : (t = term[rawtrs] { terms.add(t); }) *
;

term[RawTrs rawtrs] returns [TRSTerm t]
    : id=identifier ('(' tl=termlist[rawtrs] ')')? {
        if (rawtrs.isVariable(id)) {
            return TRSTerm.createVariable(id);
        } else {
            if (tl == null) {
                tl = TRSTerm.EMPTY_ARGS;
            }
            FunctionSymbol f = FunctionSymbol.create(id, tl.size());
            return TRSTerm.createFunctionApplication(f, tl);
        }
    }
;

termlist[RawTrs rawtrs] returns [ArrayList<TRSTerm> terms]
    @init {
        terms = new ArrayList<TRSTerm>();
    }
    :
    | t=term[rawtrs] { terms.add(t); }
      (','
            t=term[rawtrs] { terms.add(t); }
      )*
;

csstratlist[RawTrs rawtrs]
    : (
        '(' id=identifier s=csstrat ')' {
            rawtrs.addReplacementMapEntry(id, s);
        }
    )*
;

csstrat returns [ImmutableSet<Integer> s]
    @init {
        Set<Integer> stmp = new LinkedHashSet<Integer> ();
    }
    : (i=integer {stmp.add(i);})* {
        s = ImmutableCreator.create(stmp);
    }
;

listOfEdges returns [Set<Pair<Integer, Integer>> edges]
    @init {
        edges = new LinkedHashSet<Pair<Integer, Integer>>();
    }
    : edge[edges]*
;

edge[Set<Pair<Integer, Integer>> edges]
    : from=integer '->' to=integer {
        edges.add(new Pair<Integer, Integer>(from, to));
    }
; 

idlist returns [ArrayList<String> idlist = new ArrayList<String>()]
    : (id=identifier { idlist.add(id); })*
;

integer returns [int i]
    : intstring=INTEGER { i = Integer.parseInt(intstring.getText()); };

identifier returns [String s]
    : kw=keyword { s = kw; }
    | number=INTEGER { s = number.getText(); }
    | id=IDENTIFIER { s = id.getText(); }
;

keyword returns [String kw]
    : tok=(COMPLEXITY | CONSTRUCTORBASED | CONTEXTSENSITIVE | EDGES | EQUATIONS
          | GOAL | INITIAL | INNERMOST | MINIMAL | NOT | OUTERMOST | PAIRS | PARALLELINNERMOST | Q
          | RULES | STARTTERM | STRATEGY | TERMINATION | THEORY | UNRESTRICTED
          | VAR)
    { kw = tok.getText(); }
;

/* this allows language words to be used as identifiers */
/* see http://www.antlr.org/wiki/pages/viewpage.action?pageId=1741 */
/* if you update this list, also update the keyword rule above */
COMPLEXITY              : 'COMPLEXITY';
CONSTRUCTORBASED        : ('CONSTRUCTOR-BASED' | 'CONSTRUCTORBASED');
CONTEXTSENSITIVE        : 'CONTEXTSENSITIVE';
EQUATIONS               : 'EQUATIONS';
INITIAL                 : 'INITIAL';
INNERMOST               : 'INNERMOST';
GOAL                    : 'GOAL';
MINIMAL                 : 'MINIMAL';
NOT                     : 'NOT';
OUTERMOST               : 'OUTERMOST';
PAIRS                   : 'PAIRS';
PARALLELINNERMOST       : 'PARALLELINNERMOST';
Q                       : 'Q';
RULES                   : 'RULES';
EDGES                   : 'EDGES';
STARTTERM               : 'STARTTERM';
STRATEGY                : 'STRATEGY';
TERMINATION             : 'TERMINATION';
THEORY                  : 'THEORY';
UNRESTRICTED            : 'UNRESTRICTED';
VAR                     : 'VAR';

STRING
    : '"' s=(Nondq*) '"'
;
INTEGER
    : s=('0'..'9')+
;
IDENTIFIER
    : IDENTCHAR+
;

fragment IDENTCHAR         : ~(' '| '(' | ')' | '"' | '|' | ','| '\t' | '\r' | '\n');
fragment Nondq          : ~('"');

WHITESPACE : ( '\t' | ' ' | '\r' | '\n')+ { $channel = HIDDEN; };

