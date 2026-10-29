package aprove.verification.probabilistic.Termination.ADPProblem.AST.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.ADPProblem.AST.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.Processors.*;

/**
 * ADP processor that uses the decision procedure for AST of RNT PTRSs
 * (right-ground, non-overlapping, tail-recursive) inside the ADP framework.
 *
 * Rewriting with an ADP problem only manipulates annotations and flags, but performs exactly the same
 * rewrite steps as its underlying PTRS, which results from removing all annotations and flags.
 * Hence, every chain tree of the ADP problem is a rewrite tree of the underlying PTRS with the same
 * structure and probabilities, so if the underlying PTRS is AST, then the ADP problem is (innermost) AST.
 *
 * The underlying PTRS consists of the de-annotated ADPs with annotations and the rules with active flag. 
 *
 * The processor is only sound for proving AST: if the underlying PTRS is not AST, nothing can be concluded
 * for the ADP problem, as the underlying PTRS is an over-approximation of what is still possible in the ADP problem.
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class ADP_AST_DecidableRNTProcessor extends ADP_AST_ProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isAST_ADPApplicable(final ADP_AST_Problem adp) {
        final PTRSProblem underlying = getUnderlyingPTRS(adp);
        return !underlying.getPR().isEmpty() && RNTDecisionProcedure.isRNT(underlying);
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processAST_ADPProblem(final ADP_AST_Problem adp, final Abortion aborter) throws AbortionException {
        final PTRSProblem underlying = getUnderlyingPTRS(adp);
        final RNTDecisionProcedure.Verdict verdict = RNTDecisionProcedure.decide(underlying, aborter);
        if (verdict.ast) {
            return ResultFactory.proved(new ADPDecidableRNTProof(underlying, verdict, adp.isInnermost()));
        }
        return ResultFactory.unsuccessful("The underlying PTRS of the ADP problem is not AST, which does not allow any conclusion for the ADP problem.");
    }

    /**
     * @return the underlying PTRS of the ADP problem, i.e., all ADPs without annotations and flags
     *         (for basic problems, the ADPs and rules of the reachability analysis are included as well, which is sound
     *         since the chain trees of the problem are rewrite trees of this larger PTRS)
     */
    public static PTRSProblem getUnderlyingPTRS(final ADP_AST_Problem adp) {
        final Map<FunctionSymbol, FunctionSymbol> deAnnoMap = adp.getDeAnnoMap();
        final Set<ProbabilisticRule> rules = new LinkedHashSet<>();
        for (final ProbabilisticRule rule : adp.getP()) {
            rules.add(rule.removeAnnos(deAnnoMap));
        }
        for (final ProbabilisticRule rule : adp.getS()) {
            rules.add(rule.removeAnnos(deAnnoMap));
        }
        if (adp.isBasic()) {
            for (final ProbabilisticRule rule : adp.getReach()) {
                rules.add(rule.removeAnnos(deAnnoMap));
            }
            for (final ProbabilisticRule rule : adp.getReachRules()) {
                rules.add(rule.removeAnnos(deAnnoMap));
            }
        }
        return new PTRSProblem(rules, RewriteStrategy.FULL, ProbabilisticTerminationResult.AST, false);
    }

    // ================================================================================
    // Proof
    // ================================================================================

    private static final class ADPDecidableRNTProof extends ADP_AST_Proof {

        private final PTRSProblem underlying;
        private final RNTDecisionProcedure.Verdict verdict;
        private final boolean innermost;

        ADPDecidableRNTProof(final PTRSProblem underlying, final RNTDecisionProcedure.Verdict verdict, final boolean innermost) {
            this.underlying = underlying;
            this.verdict = verdict;
            this.innermost = innermost;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder s = new StringBuilder();
            s.append(o.export("We switch back from the ADP problem to its underlying PTRS, which results from removing all annotations "
                + "and flags. Every chain tree of the ADP problem is a rewrite tree of the underlying PTRS with the same structure "
                + "and probabilities, so if the underlying PTRS is AST, then the ADP problem is "
                + (this.innermost ? "innermost " : "")
                + "AST. The underlying PTRS has the following rules:"));
            s.append(o.linebreak());
            s.append(o.set(this.underlying.getPR(), Export_Util.RULES));
            s.append(o.linebreak());
            s.append(o.export("We use the decision procedure for RNT PTRSs (right-ground, non-overlapping, tail-recursive):"));
            s.append(o.paragraph());
            s.append(this.verdict.export(o));
            s.append(o.paragraph());
            s.append(o.export("Hence, the ADP problem is " + (this.innermost ? "innermost " : "") + "AST."));
            return s.toString();
        }
    }
}
