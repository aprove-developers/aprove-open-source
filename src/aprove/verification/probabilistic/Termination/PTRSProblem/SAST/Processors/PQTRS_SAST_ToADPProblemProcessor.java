package aprove.verification.probabilistic.Termination.PTRSProblem.SAST.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.complexity.Utility.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.ADPProblem.SAST.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import immutables.*;

/**
 * Processor that turns a PQTRS S into the extended Probabilistic ADP Problem ADP(S)
 *
 * @author J-C Kassing & Leon Spitzer
 * @version $Id$
 */
public class PQTRS_SAST_ToADPProblemProcessor extends Processor.ProcessorSkeleton {

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
        if (obl instanceof final PQTRSProblem pqtrs) {
            return pqtrs.getTarget() == ProbabilisticTerminationResult.SAST
                && pqtrs.QsupersetOfLhsR()
                && pqtrs.isBasic();
        }
        return false;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result process(final BasicObligation obl, final BasicObligationNode oblNode, final Abortion aborter, final RuntimeInformation rti)
        throws AbortionException {
        final PQTRSProblem ptrs = (PQTRSProblem) obl;

        if (ptrs.QsupersetOfLhsR() || !ptrs.isDuplicating()) {
            return createADPProblem(ptrs, null);
        } else if (ptrs.isBasic()) {
            final Set<Rule> rules = new LinkedHashSet<>();
            for (final var pr : ptrs.getPR()) {
                for (final var r : pr.getNonProbabilisticRepresentation()) {
                    rules.add(r);
                }
            }
            final var ruleSet = new RuleSet(ImmutableCreator.create(rules), ptrs.getDefSymbolsOfR());
            final Optional<DefaultProof> sparenessProof = new SparenessApproximation(ruleSet).run(true);
            if (sparenessProof.isPresent()) {
                return createADPProblem(ptrs, sparenessProof);
            } else {
            }
        }
        return ResultFactory.unsuccessful();
    }

    private Result createADPProblem(final PQTRSProblem ptrs, final Optional<DefaultProof> sparenessProof) {
        final var ADPData = ptrs.getProbabilisticDPs();
        final var ADPs = ADPData.x;
        final var annotator = ADPData.y;

        final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap = BidirectionalMap.create(annotator);

        // we start with an empty K
        final Set<ProbabilisticRule> k_adps = new HashSet<>();
        final ADP_SAST_Problem pdp = ADP_SAST_Problem.create(ADPs, ADPs, k_adps, ptrs, ptrs, ptrs.getStrat(), ptrs.isBasic(), annoMap);
        PQTRStoADPProblemProof proof;
        if (sparenessProof != null) {
            proof = new PQTRStoADPProblemProof(ptrs, pdp, ptrs.QsupersetOfLhsR(), ptrs.isDuplicating(), sparenessProof.get());
        } else {
            proof = new PQTRStoADPProblemProof(ptrs, pdp, ptrs.QsupersetOfLhsR(), ptrs.isDuplicating(), null);
        }

        return ResultFactory.proved(pdp, YNMImplication.EQUIVALENT, proof);
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class PQTRStoADPProblemProof extends Proof.DefaultProof {

        private final boolean innermost;
        private final boolean duplicating;
        private final Proof sparenessProof;

        PQTRStoADPProblemProof(final PQTRSProblem origPQTRS,
            final ADP_SAST_Problem newPQDP,
            final boolean innermost,
            final boolean nonduplicating,
            final DefaultProof defaultProof) {
            this.innermost = innermost;
            this.duplicating = nonduplicating;
            this.sparenessProof = defaultProof;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();

            res.append(o.paragraph());
            if (this.innermost) {
                res.append("A PQTRS (R,Q) is innermost SAST iff extended ADP(R) is innermost SAST (Chain-Criterion) ")
                    .append(o.cite(Citation.KASSING_DISS))
                    .append(".");
            } else if (!this.duplicating) {
                res.append("A non-duplicating PQTRS (R,Q) is SAST iff ADP(R) is SAST (Chain-Criterion)").append(" (!PROTOTYPE!) ").append(".");
            } else { //needs to be spare then
                res.append("A spare PQTRS (R,Q) is basic SAST iff ADP(R) is basic SAST (Chain-Criterion)").append(" (!PROTOTYPE!) ").append(".");
                res.append(o.escape("Proof of spareness:"));
                res.append(o.paragraph());
                res.append(this.sparenessProof.export(o, level));
            }
            res.append(o.linebreak());
            return res.toString();
        }
    }
}
