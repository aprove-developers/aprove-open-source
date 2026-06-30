package aprove.verification.confluence;

import aprove.prooftree.Export.Utility.Citation;
import aprove.prooftree.Export.Utility.Export_Util;
import aprove.prooftree.Proofs.Proof;
import aprove.verification.dpframework.BasicStructures.Rule;
import aprove.verification.oldframework.Utility.VerbosityLevel;

import java.util.Set;

public class RedundantRuleProof extends Proof.DefaultProof {
    private final Set<Rule> newRules;

    public RedundantRuleProof(Set<Rule> newRules) {
        this.newRules = newRules;
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {
        return o.export("The TRS can be simplified by removing redundant rules ") +
                o.cite(Citation.NAGELE15) +
                o.cond_linebreak() +
                o.export(" Continuing proof with the new rule set:") +
                o.cond_linebreak() +
                o.set(newRules, Export_Util.RULES);
    }
}