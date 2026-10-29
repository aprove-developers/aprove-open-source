package aprove.verification.probabilistic.Termination.PTRSProblem.SAST.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.Processors.*;

/**
 * Processor that decides SAST for PTRSs in RNT (right-ground, non-overlapping, tail-recursive).
 *
 * The PTRS is transformed into a stochastic context-free grammar whose expected derivation lengths e
 * are the least solution of e = 1 + B e for the moment matrix B. The expected runtime of a redex of a rule
 * kappa = l -> mu (with arguments in normal form) is e_kappa = 1 + sum_{(p:r) in mu} p * e_word(r), and the
 * PTRS is SAST iff e_max = max_kappa e_kappa is finite, which holds iff every SCC of B has spectral radius < 1.
 * Then the expected runtime of every term t is at most e_max * |pos_D(t)|. Everything is computed exactly
 * by Gaussian elimination over the rationals, see {@link RNTDecisionProcedure}.
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class PTRS_SAST_DecidableRNTDirectProcessor extends PTRS_SAST_ProblemProcessor {

    @Override
    public boolean isPTRSApplicable(final PTRSProblem R) {
        return RNTDecisionProcedure.isRNT(R);
    }

    @Override
    protected Result processPTRSProblem(final PTRSProblem R, final Abortion aborter) throws AbortionException {
        final RNTDecisionProcedure.Verdict verdict = RNTDecisionProcedure.decide(R, aborter);
        final DecidableRNTSASTProof proof = new DecidableRNTSASTProof(verdict, R.isInnermost());
        if (verdict.sast) {
            return ResultFactory.proved(proof);
        } else {
            return ResultFactory.disproved(proof);
        }
    }

    private static final class DecidableRNTSASTProof extends Proof.DefaultProof {

        private final RNTDecisionProcedure.Verdict verdict;
        private final boolean innermost;

        DecidableRNTSASTProof(final RNTDecisionProcedure.Verdict verdict, final boolean innermost) {
            this.verdict = verdict;
            this.innermost = innermost;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder s = new StringBuilder();
            s.append(this.verdict.export(o));
            s.append(o.paragraph());
            s.append(this.verdict.exportRuntime(o));
            if (this.innermost) {
                s.append(o.paragraph());
                s.append(o.export("For RNT, SAST and innermost SAST coincide, as all rewrite trees that start in right-hand sides are innermost."));
            }
            return s.toString();
        }
    }
}
