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
 * Knowledge Propagation Processor as described in Leon's master's thesis
 * (Analyzing Strong Almost-Sure Termination for Probabilistic Term Rewriting Using Dependency Pairs, 2025)
 *
 * @author J-C Kassing & Leon Spitzer
 * @version $Id$
 */
public class ADP_Cpx_KnowledgePropagationProcessor extends ADP_Cpx_ProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isCpxADP_Applicable(final ADP_Cpx_Problem pqdp) {
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
    protected Result processCpxADPProblem(final ADP_Cpx_Problem origPqdp, final Abortion aborter) throws AbortionException {
        // In this processor we move rules from S to K
        final Set<ProbabilisticRule> rulesToMove = origPqdp.getRulesWithAllPredinK();

        final ADP_Cpx_Problem newPqdp;
        newPqdp = origPqdp.getSubProblemWithMovedRules(rulesToMove);

        final boolean innermost = origPqdp.QsupersetOfLhsS();
        final CpxADP_KnowledgePropagationProof kpPproof = new CpxADP_KnowledgePropagationProof(rulesToMove);

        return ResultFactory.proved(newPqdp, BothBounds.create(), kpPproof);
    }

    // ================================================================================
    // Proof
    // ================================================================================

    private static class CpxADP_KnowledgePropagationProof extends ADP_SAST_Proof {

        private final Set<ProbabilisticRule> movedRules;

        private CpxADP_KnowledgePropagationProof(final Set<ProbabilisticRule> movedRules) {
            this.movedRules = movedRules;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();
            res.append(o.paragraph());
            res.append("We use the knowledge propagation processor " + o.cite(Citation.KASSING_DISS) + ".");
            res.append(o.linebreak());
            res.append("We can remove rules from S, if in the dependency graph no predecessor is in S ");
            res.append("(all predecessors have a known complexity bound).");
            res.append(o.linebreak());
            res.append(o.linebreak());
            res.append("Following rules are removed from S:");
            res.append(o.linebreak());
            res.append(o.set(this.movedRules, Export_Util.RULES));
            return o.export(res.toString());
        }
    }
}
