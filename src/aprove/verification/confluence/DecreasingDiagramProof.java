package aprove.verification.confluence;

import aprove.prooftree.Export.Utility.Citation;
import aprove.prooftree.Export.Utility.Export_Util;
import aprove.prooftree.Proofs.Proof;
import aprove.verification.oldframework.PropositionalLogic.Formula;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.Diophantine;
import aprove.verification.oldframework.Utility.VerbosityLevel;

public class DecreasingDiagramProof extends Proof.DefaultProof {
    private final Formula<Diophantine> constraint;

    public DecreasingDiagramProof(Formula<Diophantine> constraint) {
        this.constraint = constraint;
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {
        return o.export("The labels of the rules of the TRS are decreasing with the conditions: ") +
                o.cond_linebreak() +
                o.export(this.constraint) +
                o.cond_linebreak() +
                o.export("which are solvable. ") +
                o.export("Because the TRS is also locally confluent, this implies confluence. ") +
                o.cite(Citation.AOTO10);
    }
}
