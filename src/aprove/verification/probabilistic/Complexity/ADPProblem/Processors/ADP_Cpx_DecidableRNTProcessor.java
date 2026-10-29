package aprove.verification.probabilistic.Complexity.ADPProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Complexity.ADPProblem.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.Processors.*;

/**
 * Knowledge propagation via the exact expected-runtime analysis for RNT PTRSs
 * (right-ground, non-overlapping, tail-recursive).
 *
 * Consider an ADP problem (P, S, K) for innermost rewriting and basic start terms, and let R_S be the PTRS
 * of the ADPs in S where all annotations are removed. We require that 
 *      (1) all predecessors of S in the dependency graph are in K or S, and 
 *      (2) in the right-hand sides of R_S, all arguments of redexes of R_S are normal forms w.r.t. the rules with active flag.
 * By (1), every S-step rewrites a redex created by a K-step or by an earlier S-step.
 * By (2), the arguments of a redex created by an S-step can only be rewritten by steps with flag false, which
 * remove its annotation. If R_S is in RNT with finite e_max, the expected number of S-steps is thus at most
 * e_max * (1 + number of redexes created by K-steps), and S can be moved to K.
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class ADP_Cpx_DecidableRNTProcessor extends ADP_Cpx_ProblemProcessor {

    @Override
    public boolean isCpxADP_Applicable(final ADP_Cpx_Problem adp) {
        if (!adp.getInnermost() || !adp.isBasic() || adp.getS().isEmpty()) {
            return false;
        }
        if (!allPredecessorsInKOrS(adp)) {
            return false;
        }
        final PTRSProblem rs = getUnderlyingPTRSofS(adp);
        return RNTDecisionProcedure.isRNT(rs) && RNTDecisionProcedure.argumentsOfRedexesAreNormal(rs, adp.getSWithQ());
    }

    @Override
    protected Result processCpxADPProblem(final ADP_Cpx_Problem adp, final Abortion aborter) throws AbortionException {
        final PTRSProblem rs = getUnderlyingPTRSofS(adp);
        final RNTDecisionProcedure.Verdict verdict = RNTDecisionProcedure.decide(rs, aborter);
        if (!verdict.sast) {
            return ResultFactory.unsuccessful("The PTRS of the ADPs in S is not SAST.");
        }
        final Set<ProbabilisticRule> moved = new LinkedHashSet<>(adp.getS());
        final ADP_Cpx_Problem newProblem = adp.getSubProblemWithMovedRules(moved);
        return ResultFactory.proved(newProblem, BothBounds.create(), new ADPDecidableRNTCpxProof(moved, rs, verdict));
    }

    /**
     * @return true iff every predecessor in the dependency graph of an ADP in S is in K or in S
     *         (and every ADP in S has an annotated left-hand side)
     */
    static boolean allPredecessorsInKOrS(final ADP_Cpx_Problem adp) {
        final Map<FunctionSymbol, FunctionSymbol> deAnnoMap = adp.getDeAnnoMap();
        final Graph<ProbabilisticRule, ?> graph = adp.getDependencyGraph().getGraph();
        for (final ProbabilisticRule s : adp.getS()) {
            if (!s.isADP(deAnnoMap)) {
                return false;
            }
            final Node<ProbabilisticRule> node = graph.getNodeFromObject(s);
            if (node == null) {
                return false;
            }
            for (final Node<ProbabilisticRule> pred : graph.getIn(node)) {
                final ProbabilisticRule rule = pred.getObject();
                if (!adp.getK().contains(rule) && !adp.getS().contains(rule)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * @return the PTRS R_S of the ADPs in S without annotations
     */
    public static PTRSProblem getUnderlyingPTRSofS(final ADP_Cpx_Problem adp) {
        final Map<FunctionSymbol, FunctionSymbol> deAnnoMap = adp.getDeAnnoMap();
        final Set<ProbabilisticRule> rules = new LinkedHashSet<>();
        for (final ProbabilisticRule rule : adp.getS()) {
            rules.add(rule.removeAnnos(deAnnoMap));
        }
        return new PTRSProblem(rules, RewriteStrategy.INNERMOST, ProbabilisticTerminationResult.SAST, false);
    }

    private static final class ADPDecidableRNTCpxProof extends ADP_Cpx_Proof {

        private final Set<ProbabilisticRule> moved;
        private final PTRSProblem rs;
        private final RNTDecisionProcedure.Verdict verdict;

        ADPDecidableRNTCpxProof(final Set<ProbabilisticRule> moved, final PTRSProblem rs, final RNTDecisionProcedure.Verdict verdict) {
            this.moved = moved;
            this.rs = rs;
            this.verdict = verdict;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder s = new StringBuilder();
            s.append(o.export("We use the decision procedure for RNT PTRSs (right-ground, non-overlapping, tail-recursive): all predecessors of S in the "
                + "dependency graph are in K or S, and all arguments of redexes in the right-hand sides of S are normal forms "
                + "w.r.t. the rules with active flag. So the S-steps are evaluations of redexes created by K-steps with the "
                + "PTRS R_S of the ADPs in S where all annotations are removed:"));
            s.append(o.linebreak());
            s.append(o.set(this.rs.getPR(), Export_Util.RULES));
            s.append(o.paragraph());
            s.append(this.verdict.export(o));
            s.append(o.paragraph());
            s.append(this.verdict.exportRuntime(o));
            s.append(o.paragraph());
            s.append(o.export("The expected number of S-steps is at most e_max = " + this.verdict.eMax
                + " times (1 + the number of redexes created by K-steps). Hence, we move the following ADPs from S to K:"));
            s.append(o.linebreak());
            s.append(o.set(this.moved, Export_Util.RULES));
            return s.toString();
        }
    }
}
