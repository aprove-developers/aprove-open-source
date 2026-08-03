package aprove.verification.probabilistic.Termination.PTRSProblem.AST.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;

/**
 * Processor that transforms the analysis of <em>outermost</em> AST of a PTRS {@code P} into the
 * analysis of <em>innermost</em> AST of the transformed PTRS {@code Trans_o(P)}.
 * <p>
 * This implements the transformation {@code Trans_o} from Kassing's dissertation
 * (Section "From Outermost to Innermost Evaluation"), whose soundness theorem states
 * {@code AST_o(P) <== AST_i(Trans_o(P))}. Hence, proving innermost AST of the transformed system
 * is sufficient (but not necessary) to prove outermost AST of the original system.
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class PTRS_AST_OutermostToInnermostProcessor extends PTRS_AST_ProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isPTRSApplicable(final PTRSProblem ptrs) {
        return ptrs.isOutermost();
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result processPTRSProblem(final PTRSProblem ptrs, final Abortion aborter) throws AbortionException {
        final OutermostToInnermostTransformation.Result trans =
            OutermostToInnermostTransformation.transform(ptrs.getProbabilisticRules(), ptrs.getSignature());

        // AST_o(P) is implied by AST_i(Trans_o(P)); the transformed system is analyzed innermost.
        final PTRSProblem newptrs =
            PTRSProblem.create(trans.rules, RewriteStrategy.INNERMOST, ProbabilisticTerminationResult.AST, ptrs.isBasic());

        return ResultFactory.proved(newptrs, YNMImplication.SOUND, new OutermostToInnermostProof(trans));
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class OutermostToInnermostProof extends Proof.DefaultProof {

        private final OutermostToInnermostTransformation.Result trans;

        public OutermostToInnermostProof(final OutermostToInnermostTransformation.Result trans) {
            this.trans = trans;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            sb.append("We transform the outermost AST problem into an innermost AST problem [Kassing, Diss.]. ")
                .append("Since a PTRS P is outermost AST if the transformed PTRS Trans_o(P) is innermost AST, ")
                .append("it suffices to analyze innermost AST of the following PTRS Trans_o(P):")
                .append(o.linebreak())
                .append(o.set(this.trans.rules, Export_Util.RULES))
                .append(o.linebreak());
            return sb.toString();
        }
    }
}
