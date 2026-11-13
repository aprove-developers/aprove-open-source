package aprove.verification.probabilistic.Termination.ADPProblem.SAST.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.ADPProblem.SAST.*;
import immutables.*;

/**
 * Probability Removal Processor as described in Leon's master's thesis
 * (Analyzing Strong Almost-Sure Termination for Probabilistic Term Rewriting Using Dependency Pairs, 2025)
 *
 * @author J-C Kassing & Leon Spitzer
 * @version $Id$
 */
public class ADP_SAST_ProbabilityRemovalProcessor extends ADP_SAST_ProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isSAST_ADPApplicable(final ADP_SAST_Problem pqdp) {
        // Only applies if we restrict to innermost evaluation and basic start terms
        if (!pqdp.getInnermost() || !pqdp.isBasic()) {
            return false;
        }
        return pqdp.isNonProbabilistic();
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processSAST_ADPProblem(final ADP_SAST_Problem origPqdp, final Abortion aborter) throws AbortionException {
        final QTRSProblem newQtrs = origPqdp.getSwithQ().getNonProbAbstraction();

        final Set<ProbabilisticRule> P = origPqdp.getP();
        final Set<Rule> depPairs = new HashSet<>();
        for (final ProbabilisticRule depTuple : P) {
            for (final TRSTerm rhs : depTuple.getRight().getSupport()) {
                for (final TRSTerm annoSubterm : rhs.getAnnoSubterms(origPqdp.getDeAnnoMap())) {
                    depPairs.add(Rule.create(depTuple.getLeft(), annoSubterm));
                }
            }
        }
        final QDPProblem newqdp = QDPProblem.create(ImmutableCreator.create(depPairs), newQtrs, false);

        final SAST_ADPProbabilityRemovalProof NPPproof = new SAST_ADPProbabilityRemovalProof(origPqdp.getInnermost());

        if (origPqdp.isBasic()) {
            return ResultFactory.proved(newqdp, YNMImplication.SOUND, NPPproof);
        }
        return ResultFactory.proved(newqdp, YNMImplication.EQUIVALENT, NPPproof);
    }

    // ================================================================================
    // Proof
    // ================================================================================

    private static class SAST_ADPProbabilityRemovalProof extends ADP_SAST_Proof {

        private final boolean innermost;

        private SAST_ADPProbabilityRemovalProof(final boolean innermost) {
            this.innermost = innermost;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();
            res.append(o.paragraph());
            if (this.innermost) {
                res.append("We use the probability removal processor ").append(o.cite(Citation.FLOPS24)).append(".");
            } else { //full AST
                res.append("We use the probability removal processor ").append(" (!PROTOTYPE!) ").append(".");
            }
            res.append(o.linebreak());
            res.append("As all rules have a trivial probability (1:r), we can transform it into a non-probabilistic DP problem");

            return o.export(res.toString());
        }

    }

    public static class Arguments {

        public boolean beComplete = true;
        public boolean useApplicativeCeRules = true;
    }
}
