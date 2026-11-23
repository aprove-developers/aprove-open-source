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
 * Knowledge Propagation Processor as described in Leon's master's thesis
 * (Analyzing Strong Almost-Sure Termination for Probabilistic Term Rewriting Using Dependency Pairs, 2025)
 *
 * @author J-C Kassing & Leon Spitzer
 * @version $Id$
 */
public class ADP_SAST_KnowledgePropagationProcessor extends ADP_SAST_ProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isSAST_ADPApplicable(final ADP_SAST_Problem pqdp) {
        // Only applies if we restrict to innermost evaluation and basic start terms
        if (!pqdp.getInnermost() || !pqdp.isBasic() || pqdp.getRulesWithAllPredinK().isEmpty()) {
            return false;
        }
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processSAST_ADPProblem(final ADP_SAST_Problem origPqdp, final Abortion aborter) throws AbortionException {
        // In this processor we move rules from S to K
        final Set<ProbabilisticRule> rulesToMove = origPqdp.getRulesWithAllPredinK();

        final ADP_SAST_Problem newPqdp;
        newPqdp = origPqdp.getSubProblemWithMovedRules(rulesToMove);

        final boolean innermost = origPqdp.QsupersetOfLhsS();
        final SAST_ADPKnowledgePropagationProof URPproof = new SAST_ADPKnowledgePropagationProof(rulesToMove, innermost);

        final Result result = ResultFactory.proved(newPqdp, YNMImplication.EQUIVALENT, URPproof);
        return result;
    }

    // ================================================================================
    // Proof
    // ================================================================================

    private static class SAST_ADPKnowledgePropagationProof extends ADP_SAST_Proof {

        private final Set<ProbabilisticRule> movedRules;
        private final boolean innermost;

        private SAST_ADPKnowledgePropagationProof(final Set<ProbabilisticRule> movedRules,
            final boolean innermost) {
            this.movedRules = movedRules;
            this.innermost = innermost;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();
            res.append(o.paragraph());
            if (this.innermost) {
                res.append("We use the knowledge propagation processor ").append(o.cite(Citation.KASSING_DISS)).append(".");
            } else { //full SAST
                res.append("We use the knowledge propagation processor ").append(" (!PROTOTYPE!) ").append(".");
            }
            res.append(o.linebreak());
            res.append("We can move rules from S to K, which have in the dependency graph all predecessors in K.");
            res.append(o.linebreak());
            res.append(o.linebreak());
            res.append("Following rules in S are moved to K:");
            res.append(o.linebreak());
            res.append(o.set(this.movedRules, Export_Util.RULES));
            return o.export(res.toString());
        }
    }
}
