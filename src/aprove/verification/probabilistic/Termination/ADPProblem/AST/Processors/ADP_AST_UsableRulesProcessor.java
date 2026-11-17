package aprove.verification.probabilistic.Termination.ADPProblem.AST.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.ADPProblem.AST.*;

/**
 * Usable Rules Processor as described in Kassing's master's thesis, CADE23, and FLOPS24 for ADPs
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class ADP_AST_UsableRulesProcessor extends ADP_AST_ProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isAST_ADPApplicable(final ADP_AST_Problem qdp) {
        if (!qdp.isInnermost() && !qdp.isBasic()) {
            // no usable rules processor possible for full rewriting with arbitrary start terms
            return false;
        }
        if (qdp.isBasic()) {
            /**BASIC**/
            final Set<ProbabilisticRule> basicUsableRules = qdp.getBasicUsableRules();
            final Set<ProbabilisticRule> reachRules = qdp.getReachRules();
            // check whether we can gain something
            return basicUsableRules.size() < reachRules.size();
        } else {
            /**INNERMOST**/
            final Set<ProbabilisticRule> usableRules = qdp.getUsableRules();
            final Set<ProbabilisticRule> R = qdp.getS();
            // check whether we can gain something
            return usableRules.size() < R.size();
        }
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processAST_ADPProblem(final ADP_AST_Problem origpqdp, final Abortion aborter) throws AbortionException {
        final ADP_AST_Problem newpqdp;
        if (origpqdp.isBasic()) { /**BASIC**/
            newpqdp = origpqdp.getSubProblemWithBasicUsableRules();
        } else { /**INNERMOST**/
            newpqdp = origpqdp.getSubProblemWithUsableRules();
        }

        final AST_ADPUsableRulesProof URPproof = new AST_ADPUsableRulesProof(origpqdp);

        final Result result = ResultFactory.proved(newpqdp, YNMImplication.EQUIVALENT, URPproof);

        return result;

    }

    // ================================================================================
    // Proof
    // ================================================================================

    private static class AST_ADPUsableRulesProof extends ADP_AST_Proof {

        private final ADP_AST_Problem origQDP;

        private AST_ADPUsableRulesProof(final ADP_AST_Problem origQDP) {
            this.origQDP = origQDP;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();
            res.append(o.paragraph());
            if (this.origQDP.isInnermost()) {
                res.append("We use the usable rules processor ").append(o.cite(Citation.KASSING_DISS)).append(".");
            } else { //full AST
                res.append("We use the usable rules processor for basic start terms ").append(o.cite(Citation.JPK60)).append(".");
            }
            res.append(o.linebreak())
                .append("Hence, by the usable rules processor ")
                .append(o.cite(this.origQDP.isInnermost() ? Citation.KASSING_DISS : Citation.JPK60))
                .append(" we can deactivate the flags for all non-usable rules ")
                .append(o.cite(Citation.FROCOS05));

            return o.export(res.toString());
        }

    }
}
