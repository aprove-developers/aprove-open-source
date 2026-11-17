package aprove.verification.probabilistic.Complexity.PTRSProblem.Processors;

import java.util.*;

import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.complexity.Utility.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.Complexity.PTRSProblem.*;
import immutables.*;

/**
 * PROTOTYPE! USE WITH CAUTION!
 * @author J-C Kassing
 * @version $Id$
 */
public class PTRS_Cpx_ToParaInnermostProcessor extends PTRS_Cpx_Processor {

    @Override
    public boolean isCpxPTRSApplicable(final PTRS_Cpx_Problem R) {
        return Options.certifier == Certifier.NONE
            && R.getRewriteStrategy() != RewriteStrategy.PARALLEL_SIMULTANEOUS_INNERMOST
            && R.isNonOverlapping();
    }

    @Override
    protected Result processCpxPTRS(final PTRS_Cpx_Problem R, final Abortion aborter) throws AbortionException {
        //Since the processor is applicable, we know that R is non-overlapping.
        //Only check spareness (in case of basic start terms) or right-linearity.
        if (R.isRightLinear()) {
            final var newPTrs = PTRS_Cpx_Problem.create(ImmutableCreator.create(R.getPR()), RewriteStrategy.PARALLEL_SIMULTANEOUS_INNERMOST, R.isBasic());
            return ResultFactory.proved(newPTrs, BothBounds.create(), new CpxPTRS_ToParaInnermostProof(null, false, R));
        } else if (R.isBasic()) {
            final Set<Rule> rules = new LinkedHashSet<>();
            for (final var pr : R.getPR()) {
                for (final var r : pr.getNonProbabilisticRepresentation()) {
                    rules.add(r);
                }
            }
            final var ruleSet = new RuleSet(ImmutableCreator.create(rules), R.getDefSymbolsOfR());
            final Optional<DefaultProof> proof = new SparenessApproximation(ruleSet).run(false);
            if (proof.isPresent()) {
                final var newPTrs = PTRS_Cpx_Problem.create(ImmutableCreator.create(R.getPR()), RewriteStrategy.PARALLEL_SIMULTANEOUS_INNERMOST, R.isBasic());
                return ResultFactory.proved(newPTrs, BothBounds.create(), new CpxPTRS_ToParaInnermostProof(proof.get(), true, R));
            } else {
                return ResultFactory.unsuccessful();
            }
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    private class CpxPTRS_ToParaInnermostProof extends DefaultProof {

        Proof sparenessProof;
        boolean onlyNDProof;

        public CpxPTRS_ToParaInnermostProof(final Proof sparenessProof, final boolean onlyNDProof, final PTRS_Cpx_Problem R) {
            this.sparenessProof = sparenessProof;
            this.onlyNDProof = onlyNDProof;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder proof = new StringBuilder();
            proof.append(o.export("Switched from non-innermost to simultaneous-innermost rewriting" + o.cite(Citation.FoSSaCS24) + "."));
            proof.append(o.paragraph());
            proof.append(o.escape("The system is orthogonal and "));
            if (this.onlyNDProof) {
                proof.append(o.escape("spare"));
            } else {
                proof.append(o.escape("right-linear"));
            }
            proof.append(o.escape(", so its complexity is bounded by its simultaneous-innermost complexity."));
            proof.append(o.newline());
            if (this.onlyNDProof) {
                proof.append(o.escape("Proof of spareness:"));
                proof.append(o.paragraph());
                proof.append(this.sparenessProof.export(o, level));
            }
            return proof.toString();
        }

    }

}
