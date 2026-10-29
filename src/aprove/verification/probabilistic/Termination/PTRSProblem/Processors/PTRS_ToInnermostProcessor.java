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
 * Switch from full to innermost evaluation as in [FoSSaCS24].
 *
 * @author J-C Kassing & Florian Frohn
 * @version $Id$
 */
public class PTRS_ToInnermostProcessor extends PTRS_ProblemProcessor {

    @Override
    public boolean isPTRSApplicable(final PTRSProblem R) {
        if (Options.certifier != Certifier.NONE
            || R.getRewriteStrategy() == RewriteStrategy.INNERMOST
            || !(R.isLeftLinear())
            || !(R.isNonOverlapping())) {
            return false;
        }

        //For strategies other than full rewriting (e.g., outermost), the equivalence to
        //innermost rewriting additionally requires non-erasingness.
        if (R.getRewriteStrategy() != RewriteStrategy.FULL && !(R.isNonErasing())) {
            return false;
        }

        return true;
    }

    @Override
    protected Result processPTRSProblem(final PTRSProblem R, final Abortion aborter) throws AbortionException {
        //Since the processor is applicable, we know that R is left-linear and non-overlapping
        //(and non-erasing in case of a strategy other than full rewriting).
        //Only check spareness (in case of full rewriting with basic start terms) or right-linearity.
        if (R.isRightLinear()) {
            final var newPTrs = PTRSProblem.create(ImmutableCreator.create(R.getPR()), RewriteStrategy.INNERMOST, R.getTarget(), R.isBasic());
            return ResultFactory.proved(newPTrs, YNMImplication.EQUIVALENT, new ToInnermostProof(null, false, R));
        } else if (R.getRewriteStrategy() == RewriteStrategy.FULL && R.isBasic()) {
            final Set<Rule> rules = new LinkedHashSet<>();
            for (final var pr : R.getPR()) {
                for (final var r : pr.getNonProbabilisticRepresentation()) {
                    rules.add(r);
                }
            }
            final var ruleSet = new RuleSet(ImmutableCreator.create(rules), R.getDefSymbolsOfR());
            final Optional<DefaultProof> proof = new SparenessApproximation(ruleSet).run(false);
            if (proof.isPresent()) {
                final var newPTrs = PTRSProblem.create(ImmutableCreator.create(R.getPR()), RewriteStrategy.INNERMOST, R.getTarget(), R.isBasic());
                return ResultFactory.proved(newPTrs, YNMImplication.EQUIVALENT, new ToInnermostProof(proof.get(), true, R));
            } else {
                return ResultFactory.unsuccessful();
            }
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    private class ToInnermostProof extends DefaultProof {

        Proof sparenessProof;
        boolean onlyNDProof;
        PTRSProblem R;

        public ToInnermostProof(final Proof sparenessProof, final boolean onlyNDProof, final PTRSProblem R) {
            this.sparenessProof = sparenessProof;
            this.onlyNDProof = onlyNDProof;
            this.R = R;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder proof = new StringBuilder();
            proof.append(o.export("Switched from non-innermost to innermost rewriting" + o.cite(Citation.FoSSaCS24) + "."));
            proof.append(o.paragraph());
            proof.append(o.escape("The system is non-overlapping, left-linear and "));
            if (this.onlyNDProof) {
                proof.append(o.escape("spare"));
            } else {
                proof.append(o.escape("right-linear"));
            }
            if (this.R.getRewriteStrategy() != RewriteStrategy.FULL) {
                proof.append(o.escape(" and non-erasing"));
                proof.append(o.escape(", so it is " + this.R.getRewriteStrategy().getRepresentation() + " "
                    + this.R.getTarget() + " iff it is innermost " + this.R.getTarget() + "."));
            } else {
                proof.append(o.escape(", so it is " + this.R.getTarget() + " iff it is innermost " + this.R.getTarget() + "."));
            }
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
