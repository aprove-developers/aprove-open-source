package aprove.verification.probabilistic.Termination.PTRSProblem.AST.Processors;

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
import aprove.verification.probabilistic.Termination.ADPProblem.AST.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import immutables.*;

/**
 * Processor that turns a PQTRS S into the Probabilistic ADP Problem ADP(S)
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class PQTRS_AST_ToADPProblemProcessor extends Processor.ProcessorSkeleton {

    // ================================================================================
    // isApplicable
    // ================================================================================

    /**
     * The ADP framework is applicable in the innermost case,
     * for full rewriting if the PQTRS is non-duplicating,
     * and for full rewriting w.r.t. basic start terms if the PQTRS is weakly-spare.
     *
     * We check for weak-spareness in the application of the processor
     */
    @Override
    public boolean isApplicable(final BasicObligation obl) {
        if (obl instanceof final PQTRSProblem pqtrs) {
            if (pqtrs.getTarget() != ProbabilisticTerminationResult.AST) { //Only for AST
                return false;
            }
            if (pqtrs.QsupersetOfLhsR()) { /**INNERMOST**/
                return true;
            } else if (pqtrs.isBasic()) { /**BASIC**/
                return true; //Check for spareness in processing
            } else { /**FULL**/
                return !pqtrs.isDuplicating();
            }
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

        ADP_AST_Problem pdp;
        if (ptrs.isBasic() & !ptrs.QsupersetOfLhsR()) { /**BASIC**/
            //Framework for iAST is better than for bAST, hence use bAST only if it is not innermost
            pdp = ADP_AST_Problem.createBasic(ADPs, ADPs, ptrs, ptrs, ptrs.getStrat(), annoMap);
        } else { /**FULL and INNERMOST**/
            pdp = ADP_AST_Problem.create(ADPs, ptrs, ptrs.getStrat(), annoMap);
        }
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
            final ADP_AST_Problem newPQDP,
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
                res.append("A PQTRS (R,Q) is innermost AST iff ADP(R) is innermost AST (Chain-Criterion) ").append(o.cite(Citation.KASSING_DISS)).append(".");
            } else if (!this.duplicating) {
                res.append("A non-duplicating PQTRS (R,Q) is AST iff ADP(R) is AST (Chain-Criterion) ").append(o.cite(Citation.KASSING_DISS)).append(".");
            } else { //needs to be spare then
                res.append("A spare PQTRS (R,Q) is basic AST iff ADP(R) is basic AST (Chain-Criterion) ").append(o.cite(Citation.JPK60)).append(".");
                res.append(o.escape("Proof of spareness:"));
                res.append(o.paragraph());
                res.append(this.sparenessProof.export(o, level));
            }

            return res.toString();
        }
    }
}
