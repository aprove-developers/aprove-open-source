package aprove.verification.confluence;

import java.util.Map;
import java.util.Set;

import aprove.prooftree.Export.Utility.Citation;
import aprove.prooftree.Export.Utility.Export_Util;
import aprove.prooftree.Proofs.Proof;
import aprove.verification.dpframework.BasicStructures.Rule;
import aprove.verification.oldframework.BasicStructures.FunctionSymbol;
import aprove.verification.oldframework.Utility.VerbosityLevel;

public class QuasiLinearLinearizedDecreasingProof extends Proof.DefaultProof {

    private final Map<FunctionSymbol, QuasiLinearLinearizedDecreasingProcessor.NestedSort> sorts;
    private final Set<Rule> nonLinearRules;

    public QuasiLinearLinearizedDecreasingProof(Map<FunctionSymbol, QuasiLinearLinearizedDecreasingProcessor.NestedSort> sorts, Set<Rule> nonLinearRules) {
        this.sorts = sorts;
        this.nonLinearRules = nonLinearRules;
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {
        StringBuilder s = new StringBuilder();
        s.append(o.export("Sort assignment:"));
        s.append(o.linebreak());
        for (var sortAssignment : this.sorts.entrySet()) {
            s.append(o.export(sortAssignment.getKey()));
            s.append(o.export(": "));
            s.append(o.export(sortAssignment.getValue()));
            s.append(o.linebreak());
        }

        s.append(o.export("Non-linear rules:"));
        s.append(o.linebreak());
        s.append(o.set(this.nonLinearRules, Export_Util.RULES));

        s.append(o.export("R^t is linearized-decreasing. "));
        s.append(o.export("If R^t is also innermost normalizing, then this implies confluence."));
        s.append(o.cond_linebreak());
        s.append(o.export("Approximate innermost normalization by innermost termination."));

        s.append(o.cite(Citation.AOTO_TOYAMA_UCHIMA14));
        return s.toString();
    }
}
