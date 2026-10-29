package aprove.verification.probabilistic.Complexity.PTRSProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Complexity.PTRSProblem.*;

/**
 * Processor that transforms the analysis of the <em>outermost</em> complexity of a PTRS {@code P}
 * into the analysis of the <em>innermost</em> complexity of the transformed PTRS {@code Trans_o(P)}.
 * <p>
 * This applies the transformation {@code Trans_o} from Kassing's dissertation
 * (Section "From Outermost to Innermost Evaluation"). Every outermost rewrite step of {@code P} is
 * simulated by one or more innermost steps of {@code Trans_o(P)}, so the innermost derivation length
 * of {@code Trans_o(P)} is an upper bound on the outermost derivation length of {@code P}. Hence an
 * upper complexity bound obtained for {@code Trans_o(P)} is a sound upper bound for {@code P}
 * (lower bounds do not carry over).
 *
 * @author J-C Kassing
 */
public class PTRS_Cpx_OutermostToInnermostProcessor extends PTRS_Cpx_Processor {

    @Override
    protected boolean isCpxPTRSApplicable(final PTRS_Cpx_Problem obl) {
        return obl.isOutermost();
    }

    @Override
    protected Result processCpxPTRS(final PTRS_Cpx_Problem cpxTrs, final Abortion aborter) throws AbortionException {
        final OutermostToInnermostTransformation.Result trans =
            OutermostToInnermostTransformation.transform(cpxTrs.getProbabilisticRules(), cpxTrs.getSignature());

        final PTRS_Cpx_Problem newObl = PTRS_Cpx_Problem.create(trans.rules, RewriteStrategy.INNERMOST, cpxTrs.isBasic());

        return ResultFactory.proved(newObl, SoundUpperUnsoundLowerBound.create(), new OutermostToInnermostProof(trans));
    }

    // ================================================================================
    // Proof
    // ================================================================================

    private static class OutermostToInnermostProof extends DefaultProof {

        private final OutermostToInnermostTransformation.Result trans;

        private OutermostToInnermostProof(final OutermostToInnermostTransformation.Result trans) {
            this.trans = trans;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append("We transform the outermost complexity problem into an innermost complexity problem [Kassing, Diss.]. ")
                .append("Each outermost rewrite step of P is simulated by one or more innermost steps of the transformed PTRS Trans_o(P), ")
                .append("so an upper bound on the innermost complexity of Trans_o(P) is a sound upper bound on the outermost complexity of P. ")
                .append("The transformed PTRS Trans_o(P) has the following rules:")
                .append(o.cond_linebreak())
                .append(o.set(this.trans.rules, Export_Util.RULES))
                .append(o.cond_linebreak());
            return sb.toString();
        }
    }
}
