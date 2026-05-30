package aprove.verification.confluence;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.FunctionSymbol;
import aprove.verification.oldframework.Utility.*;


public class NotWCRProof extends DefaultProof {
    private final JoinableResult.WcrCounterExample result;

    public NotWCRProof(JoinableResult.WcrCounterExample result) {
        this.result = result;
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {
        if (result instanceof JoinableResult.WcrCounterExample.NonJoinable(
                aprove.verification.confluence.Utility.CriticalPairInfo criticalPairInfo
        )) {
            return o.export("The TRS is not locally confluent (WCR):") +
                o.cond_linebreak() +
                o.export("These are the Rules causing the unjoinable critical Pair:") +
                o.cond_linebreak() +
                o.set(Set.of(criticalPairInfo.sRule(), criticalPairInfo.tRule()), Export_Util.RULES) +
                o.cond_linebreak() +
                o.export("This leads to the following divergence:") +
                o.cond_linebreak() +
                o.cond_linebreak() +
                o.export(criticalPairInfo.divergence()) +
                o.export(" ->* <") +
                o.export(criticalPairInfo.s()) +
                o.export(", ") +
                o.export(criticalPairInfo.t()) +
                o.export(">");

        } else if (result instanceof JoinableResult.WcrCounterExample.InvalidRootSymbol(
                GeneralizedRule sRule, GeneralizedRule tRule, FunctionSymbol f, FunctionSymbol g
        )) {
            return o.export("There are invalid root symbols in the Rules: ") +
                    o.set(Set.of(sRule, tRule), Export_Util.RULES) +
                    o.cond_linebreak() +
                    o.export("The invalid root symbols are: ") +
                    o.export(f) +
                    o.export(" and ") +
                    o.export(g);
        }

        return "";
    }
}
