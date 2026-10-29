package aprove.verification.probabilistic.Termination.PTRSProblem.AST.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.Processors.*;

/**
 * Processor that decides AST for PTRSs in RNT (right-ground, non-overlapping, tail-recursive)
 * via the transformation to stochastic context-free grammars.
 *
 * The spectral radius condition is decided exactly by Gaussian elimination over the rationals,
 * see {@link RNTDecisionProcedure}.
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class PTRS_AST_DecidableRNTDirectProcessor extends PTRS_AST_ProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isPTRSApplicable(final PTRSProblem R) {
        return RNTDecisionProcedure.isRNT(R);
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processPTRSProblem(final PTRSProblem R, final Abortion aborter) throws AbortionException {
        final RNTDecisionProcedure.Verdict verdict = RNTDecisionProcedure.decide(R, aborter);
        final DecidableRNTDirectProof proof = new DecidableRNTDirectProof(verdict, R.isInnermost());
        if (verdict.ast) {
            return ResultFactory.proved(proof);
        } else {
            return ResultFactory.disproved(proof);
        }
    }

    // ================================================================================
    // Proof
    // ================================================================================

    private static final class DecidableRNTDirectProof extends Proof.DefaultProof {

        private final RNTDecisionProcedure.Verdict verdict;
        private final boolean innermost;

        DecidableRNTDirectProof(final RNTDecisionProcedure.Verdict verdict, final boolean innermost) {
            this.verdict = verdict;
            this.innermost = innermost;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder s = new StringBuilder();
            s.append(this.verdict.export(o));
            if (this.innermost) {
                s.append(o.paragraph());
                s.append(o.export("For RNT, AST and innermost AST coincide, as all rewrite trees that start in right-hand sides are innermost."));
            }
            return s.toString();
        }
    }
}
