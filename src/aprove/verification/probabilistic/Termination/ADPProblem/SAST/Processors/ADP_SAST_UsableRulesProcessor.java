package aprove.verification.probabilistic.Termination.ADPProblem.SAST.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.ADPProblem.SAST.*;

/**
 * Usable Rules Processor as described in Leon's master's thesis
 * (Analyzing Strong Almost-Sure Termination for Probabilistic Term Rewriting Using Dependency Pairs, 2025)
 *
 * @author J-C Kassing & Leon Spitzer
 * @version $Id$
 */
public class ADP_SAST_UsableRulesProcessor extends ADP_SAST_ProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isSAST_ADPApplicable(final ADP_SAST_Problem qdp) {
        // Only applies if we restrict to innermost evaluation and basic start terms
        if (!qdp.getInnermost() || !qdp.isBasic()) {
            return false;
        }
        final Set<ProbabilisticRule> usableRules = qdp.getBasicUsableRules();
        final Set<ProbabilisticRule> R = qdp.getSWithQ();

        // check whether we can gain something
        if (usableRules.size() >= R.size()) {
            return false;
        }

        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processSAST_ADPProblem(final ADP_SAST_Problem origpqdp, final Abortion aborter) throws AbortionException {
        final ADP_SAST_Problem newpqdp;
        if (origpqdp.isBasic() && !origpqdp.getInnermost()) {
            newpqdp = origpqdp.getSubProblemWithBasicUsableRules();
        } else {
            newpqdp = origpqdp.getSubProblemWithUsableRules();
        }

        final SAST_ADPUsableRulesProof URPproof = new SAST_ADPUsableRulesProof(origpqdp, newpqdp);

        final Result result = ResultFactory.proved(newpqdp, YNMImplication.EQUIVALENT, URPproof);

        return result;

    }

    // ================================================================================
    // Proof
    // ================================================================================

    private static class SAST_ADPUsableRulesProof extends ADP_SAST_Proof {

        private final ADP_SAST_Problem origQDP;
        private Set<ProbabilisticRule> old_usableRules;
        private Set<ProbabilisticRule> new_usableRules;
        private Set<ProbabilisticRule> rules_removed_from_usable;

        private SAST_ADPUsableRulesProof(final ADP_SAST_Problem origQDP, final ADP_SAST_Problem newQDP) {
            this.origQDP = origQDP;
            this.new_usableRules = newQDP.getSwithQ().getProbabilisticRules();
            this.old_usableRules = origQDP.getSwithQ().getProbabilisticRules();
            this.rules_removed_from_usable = new HashSet<>();
            for (final ProbabilisticRule rule : this.old_usableRules) {
                if (!this.new_usableRules.contains(rule)) {
                    this.rules_removed_from_usable.add(rule);
                }
            }
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();
            res.append(o.paragraph());
            if (this.origQDP.getInnermost()) {
                res.append("We use the usable rules processor ").append(o.cite(Citation.KASSING_DISS)).append(".");
            } else { //full SAST
                res.append("We use the usable rules processor for basic start terms ").append(" (!PROTOTYPE!) ").append(".");
            }
            res.append(o.linebreak())
                .append("Hence, by the usable rules processor ")
                .append(o.cite(this.origQDP.getInnermost() ? Citation.KASSING_DISS : Citation.FLOPS24))
                .append(" we can deactivate the flags for all non-usable rules ")
                .append(o.cite(Citation.FROCOS05))
                .append(o.linebreak());

            res.append(o.linebreak());
            res.append("Rules which have been flagged as non usable in this step:");
            res.append(o.linebreak());
            res.append(o.set(this.rules_removed_from_usable, Export_Util.RULES));

            return o.export(res.toString());
        }

    }
}
