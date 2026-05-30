/*package aprove.verification.confluence;

import aprove.prooftree.Export.ProofPurposeDescriptors.DefaultProofPurposeDescriptor;
import aprove.prooftree.Export.ProofPurposeDescriptors.ProofPurposeDescriptor;
import aprove.prooftree.Export.Utility.Export_Util;
import aprove.prooftree.Obligations.DefaultBasicObligation;
import aprove.verification.dpframework.BasicStructures.Rule;
import aprove.verification.oldframework.BasicStructures.FunctionSymbol;
import immutables.ImmutableSet;

public class DecreasingDiagramProblem extends DefaultBasicObligation {
    private final ConfTRSProblem confTRSProblem;

    public DecreasingDiagramProblem(ConfTRSProblem confTRSProblem) {
        super("Confluence", "DecreasingDiagrams");
        this.confTRSProblem = confTRSProblem;
    }

    @Override
    public String getStrategyName() {
        return "conf_trs_decreasing_diagram";
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Decreasing diagram analysis via rule labelling technique");
    }

    @Override
    public String export(Export_Util eu) {
        var sb = new StringBuilder();
        sb.append(eu.export("Decreasing Diagram Analysis via Rule Labelling Technique"));
        sb.append(eu.cond_linebreak());
        if (this.getRules().isEmpty()) {
            sb.append("R is empty.");
            sb.append(eu.linebreak());
        } else {
            sb.append(eu.export("The TRS R consists of the following rules:"));
            sb.append(eu.cond_linebreak());
            sb.append(eu.set(getRules(), Export_Util.RULES));
            sb.append(eu.cond_linebreak());
        }

        return sb.toString();
    }

    public ImmutableSet<FunctionSymbol> getFunctionSymbols() {
        return confTRSProblem.getDefinedSymbolsOfR();
    }

    public ImmutableSet<Rule> getRules() {
        return confTRSProblem.getRules();
    }

    public CriticalPairs getCriticalPairs() {
        return confTRSProblem.getCriticalPairs();
    }
}
*/