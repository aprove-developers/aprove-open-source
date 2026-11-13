package aprove.verification.probabilistic.Complexity.ADPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Complexity.ADPProblem.*;
import aprove.verification.probabilistic.Termination.ADPProblem.SAST.*;

/**
 * Usable Rules Processor as described in Leon's master's thesis
 * (Analyzing Strong Almost-Sure Termination for Probabilistic Term Rewriting Using Dependency Pairs, 2025)
 *
 * @author J-C Kassing & Leon Spitzer
 * @version $Id$
 */
public class ADP_Cpx_UsableRulesProcessor extends ADP_Cpx_ProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isCpxADP_Applicable(final ADP_Cpx_Problem qdp) {
        // Only applies if we restrict to innermost evaluation and basic start terms
        if (!qdp.getInnermost() || !qdp.isBasic()) {
            return false;
        }
        final Set<ProbabilisticRule> usableRules = qdp.getUsableRules();
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
    protected Result processCpxADPProblem(final ADP_Cpx_Problem origpqdp, final Abortion aborter) throws AbortionException {
        final ADP_Cpx_Problem newpqdp = origpqdp.getSubProblemWithUsableRules();

        final CpxADP_UsableRulesProof urProof = new CpxADP_UsableRulesProof(origpqdp, newpqdp);

        return ResultFactory.proved(newpqdp, BothBounds.create(), urProof);
    }

    // ================================================================================
    // Proof
    // ================================================================================

    private static class CpxADP_UsableRulesProof extends ADP_SAST_Proof {

        private Set<ProbabilisticRule> old_usableRules;
        private Set<ProbabilisticRule> new_usableRules;
        private Set<ProbabilisticRule> rules_removed_from_usable;

        private CpxADP_UsableRulesProof(final ADP_Cpx_Problem origQDP, final ADP_Cpx_Problem newQDP) {
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
            res.append("We use the usable rules processor " + o.cite(Citation.KASSING_DISS) + ".");
            res.append(o.linebreak());
            res.append("We can deactivate the flags for all non-usable rules ");
            res.append(o.cite(Citation.FROCOS05));
            res.append(o.linebreak());

            res.append(o.linebreak());
            res.append("Rules which have been flagged as non usable in this step:");
            res.append(o.linebreak());
            res.append(o.set(this.rules_removed_from_usable, Export_Util.RULES));

            return o.export(res.toString());
        }

    }
}
