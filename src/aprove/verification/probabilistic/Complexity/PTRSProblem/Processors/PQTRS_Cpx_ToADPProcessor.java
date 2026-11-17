package aprove.verification.probabilistic.Complexity.PTRSProblem.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Complexity.ADPProblem.*;
import aprove.verification.probabilistic.Complexity.PTRSProblem.*;

/**
 * Processor that turns a PQTRS S into the extended Probabilistic ADP Problem ADP(S)
 *
 * @author J-C Kassing & Leon Spitzer
 * @version $Id$
 */
public class PQTRS_Cpx_ToADPProcessor extends Processor.ProcessorSkeleton {

    // ================================================================================
    // isApplicable
    // ================================================================================

    /**
     * The SAST ADP framework is only applicable in the *innermost* case with *basic* start terms
     *
     * We check for weak-spareness in the application of the processor
     */
    @Override
    public boolean isApplicable(final BasicObligation obl) {
        if (obl instanceof final PQTRS_Cpx_Problem pqtrs) {
            return pqtrs.QsupersetOfLhsR() && pqtrs.isBasic();
        }
        return false;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result process(final BasicObligation obl, final BasicObligationNode oblNode, final Abortion aborter, final RuntimeInformation rti)
        throws AbortionException {
        final PQTRS_Cpx_Problem ptrs = (PQTRS_Cpx_Problem) obl;
        return createADPProblem(ptrs);
    }

    private Result createADPProblem(final PQTRS_Cpx_Problem ptrs) {
        final var ADPData = ptrs.getProbabilisticDPs();
        final var ADPs = ADPData.x;
        final var annotator = ADPData.y;

        final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap = BidirectionalMap.create(annotator);

        // we start with an empty K
        final Set<ProbabilisticRule> k_adps = new HashSet<>();
        final ADP_Cpx_Problem pdp = ADP_Cpx_Problem.create(ADPs, ADPs, k_adps, ptrs, ptrs.getStrat(), ptrs.isBasic(), annoMap);
        CpxPQTRS_ToADPProblemProof proof;

        proof = new CpxPQTRS_ToADPProblemProof(ptrs, pdp, ptrs.QsupersetOfLhsR(), ptrs.isDuplicating());

        return ResultFactory.proved(pdp, BothBounds.create(), proof);
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class CpxPQTRS_ToADPProblemProof extends Proof.DefaultProof {

        private final ADP_Cpx_Problem newPQDP;

        CpxPQTRS_ToADPProblemProof(final PQTRS_Cpx_Problem origPQTRS, final ADP_Cpx_Problem newPQDP, final boolean innermost, final boolean nonduplicating) {
            this.newPQDP = newPQDP;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();

            res.append(o.paragraph());
            res.append("The complexity of a PQTRS (R,Q) is equivalent to the complexity of the ADP Problem A(R) (Chain-Criterion) ")
                .append(o.cite(Citation.KASSING_DISS))
                .append(".");
            res.append(o.linebreak());
            res.append("The ADPs are:");
            res.append(o.linebreak());
            res.append(this.newPQDP.export(o));

            return res.toString();
        }
    }
}
