package aprove.verification.probabilistic.Termination.PTRSProblem.Processors;

import java.util.*;

import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.Utility.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import immutables.*;

/**
 * Switch from innermost to full (non-innermost) evaluation -- the inverse of
 * {@link PTRS_ToInnermostProcessor}. For the class where the strategies coincide
 * (left-linear, non-overlapping, and either right-linear or basic + spare) the equivalence
 * {@code AST(R) <=> AST_i(R)} (resp. {@code SAST}) is an <em>iff</em> [FoSSaCS24], so switching
 * innermost to full is EQUIVALENT and hence sound in both directions.
 * <p>
 * In practice this is only <em>beneficial for disproving</em>: the random-walk based disproving
 * techniques (Kassing's dissertation, "Disproving Termination") are stronger for full rewriting,
 * so moving an innermost (S)AST problem to full lets them disprove it via the equivalent full system.
 *
 * @author J-C Kassing &amp; Florian Frohn
 * @version $Id$
 */
public class PTRS_ToFullProcessor extends PTRS_ProblemProcessor {

    @Override
    public boolean isPTRSApplicable(final PTRSProblem R) {
        if (Options.certifier != Certifier.NONE
            || !(R.isLeftLinear())
            || !(R.isNonOverlapping())) {
            return false;
        }

        final RewriteStrategy strat = R.getRewriteStrategy();
        if (strat == RewriteStrategy.INNERMOST) {
            // full AST <=> innermost AST for the left-linear, non-overlapping, right-linear/spare class.
            return true;
        }
        if (strat == RewriteStrategy.OUTERMOST) {
            // full AST <=> outermost AST additionally requires the system to be non-erasing
            // (Thm. properties-AST-vs-wAST); otherwise moving to full is unsound for outermost.
            // The remaining requirement (right-linearity) is checked in processPTRSProblem.
            return R.isNonErasing();
        }
        // Already full, or an unsupported strategy.
        return false;
    }

    @Override
    protected Result processPTRSProblem(final PTRSProblem R, final Abortion aborter) throws AbortionException {
        //Since the processor is applicable, we know that R is left-linear and non-overlapping (and,
        //for outermost, non-erasing). full AST <=> innermost/outermost AST holds if additionally the
        //system is right-linear; for innermost we may instead use spareness on basic start terms.
        if (R.isRightLinear()) {
            final var newPTrs = PTRSProblem.create(ImmutableCreator.create(R.getPR()), RewriteStrategy.FULL, R.getTarget(), R.isBasic());
            return ResultFactory.proved(newPTrs, YNMImplication.EQUIVALENT, new ToFullProof(null, false, R));
        } else if (R.getRewriteStrategy() == RewriteStrategy.INNERMOST && R.isBasic()) {
            final Set<Rule> rules = new LinkedHashSet<>();
            for (final var pr : R.getPR()) {
                for (final var r : pr.getNonProbabilisticRepresentation()) {
                    rules.add(r);
                }
            }
            final var ruleSet = new RuleSet(ImmutableCreator.create(rules), R.getDefSymbolsOfR());
            final Optional<DefaultProof> proof = new SparenessApproximation(ruleSet).run(false);
            if (proof.isPresent()) {
                final var newPTrs = PTRSProblem.create(ImmutableCreator.create(R.getPR()), RewriteStrategy.FULL, R.getTarget(), R.isBasic());
                return ResultFactory.proved(newPTrs, YNMImplication.EQUIVALENT, new ToFullProof(proof.get(), true, R));
            } else {
                return ResultFactory.unsuccessful();
            }
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    private class ToFullProof extends DefaultProof {

        Proof sparenessProof;
        boolean onlyNDProof;
        PTRSProblem R;

        public ToFullProof(final Proof sparenessProof, final boolean onlyNDProof, final PTRSProblem R) {
            this.sparenessProof = sparenessProof;
            this.onlyNDProof = onlyNDProof;
            this.R = R;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final String from = this.R.getRewriteStrategy() == RewriteStrategy.OUTERMOST ? "outermost" : "innermost";
            final StringBuilder proof = new StringBuilder();
            proof.append(o.export("Switched from " + from + " to full (non-innermost) rewriting" + o.cite(Citation.FoSSaCS24) + "."));
            proof.append(o.paragraph());
            proof.append(o.escape("The system is non-overlapping, left-linear, "));
            if (this.onlyNDProof) {
                proof.append(o.escape("spare"));
            } else {
                proof.append(o.escape("right-linear"));
            }
            if (this.R.getRewriteStrategy() == RewriteStrategy.OUTERMOST) {
                proof.append(o.escape(" and non-erasing"));
            }
            proof.append(o.escape(", so it is " + from + " " + this.R.getTarget() + " iff it is " + this.R.getTarget() + "."));
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
