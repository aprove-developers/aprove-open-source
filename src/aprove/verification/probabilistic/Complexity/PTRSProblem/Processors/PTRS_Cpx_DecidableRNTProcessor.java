package aprove.verification.probabilistic.Complexity.PTRSProblem.Processors;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Complexity.PTRSProblem.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.Processors.*;

/**
 * Processor that computes bounds on the expected runtime of PTRSs in RNT
 * (right-ground, non-overlapping, tail-recursive) by the exact decision procedure of {@link RNTDecisionProcedure}.
 *
 * Let e_max be the maximal expected runtime of a redex (with arguments in normal form) of a rule.
 * If e_max is finite, then the expected runtime of every term t is at most e_max * |pos_D(t)|. Hence, the expected
 * runtime complexity (basic start terms, which contain exactly one defined symbol) is bounded by the constant e_max,
 * and the expected derivational complexity is linear. If e_max is infinite, then there is a ground instance of a
 * left-hand side whose arguments are constructor terms (a basic term) with infinite expected runtime, so both the
 * expected runtime and the expected derivational complexity are infinite.
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class PTRS_Cpx_DecidableRNTProcessor extends PTRS_Cpx_Processor {

    @Override
    protected boolean isCpxPTRSApplicable(final PTRS_Cpx_Problem obl) {
        switch (obl.getRewriteStrategy()) {
            case FULL, INNERMOST, OUTERMOST -> {
                return RNTDecisionProcedure.isRNT(toPTRSProblem(obl));
            }
            default -> {
                return false;
            }
        }
    }

    @Override
    protected Result processCpxPTRS(final PTRS_Cpx_Problem obl, final Abortion aborter) throws AbortionException {
        final PTRSProblem R = toPTRSProblem(obl);
        final RNTDecisionProcedure.Verdict verdict = RNTDecisionProcedure.decide(R, aborter);
        final ComplexityYNM value;
        final boolean sizeBoundedTerms = !obl.isBasic() && hasOnlyConstantDefinedSymbolsAndUnaryConstructors(obl);
        if (!verdict.sast) {
            value = ComplexityYNM.INFINITE;
        } else if (obl.isBasic() || sizeBoundedTerms) {
            // basic start terms contain exactly one defined symbol; if all defined symbols are constants and no symbol
            // has an arity > 1, then every term contains at most one defined symbol as well
            value = ComplexityYNM.createUpper(ComplexityValue.constant(verdict.eMaxCeiling()));
        } else if (hasPackingSymbol(obl)) {
            // a symbol of arity >= 2 allows terms of size n with Omega(n) redexes l sigma (with constructor arguments) at parallel
            // positions, each of which needs at least one step in every fully evaluated (innermost) rewrite tree:
            // the expected derivational complexity is linear
            value = ComplexityYNM.create(ComplexityValue.fixedDegreePoly(1), ComplexityValue.fixedDegreePoly(1));
        } else {
            value = ComplexityYNM.createUpper(ComplexityValue.fixedDegreePoly(1));
        }
        return ResultFactory.provedWithValue(value,
            new DecidableRNTCpxProof(verdict, obl.isBasic(), sizeBoundedTerms, hasPackingSymbol(obl), obl.getRewriteStrategy(), value));
    }

    /**
     * @return true iff the signature contains a symbol of arity >= 2 below which Omega(n) parallel redexes can be placed:
     *         a constructor (for every strategy), or a defined symbol (for full and innermost rewriting, where the inner
     *         redexes have to be evaluated and cannot be erased by an outer step first)
     */
    private static boolean hasPackingSymbol(final PTRS_Cpx_Problem obl) {
        for (final FunctionSymbol f : obl.getSignature()) {
            if (f.getArity() >= 2) {
                if (!obl.getDefSymbolsOfR().contains(f) || obl.getRewriteStrategy() != RewriteStrategy.OUTERMOST) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * @return true iff every defined symbol is a constant and every symbol has arity <= 1, i.e., every term contains at most
     *         one defined symbol
     */
    private static boolean hasOnlyConstantDefinedSymbolsAndUnaryConstructors(final PTRS_Cpx_Problem obl) {
        for (final FunctionSymbol f : obl.getSignature()) {
            if (f.getArity() > 1) {
                return false;
            }
            if (f.getArity() == 1 && obl.getDefSymbolsOfR().contains(f)) {
                return false;
            }
        }
        return true;
    }

    private static PTRSProblem toPTRSProblem(final PTRS_Cpx_Problem obl) {
        return new PTRSProblem(obl.getPR(), obl.getRewriteStrategy(), ProbabilisticTerminationResult.SAST, obl.isBasic());
    }

    private static final class DecidableRNTCpxProof extends PTRS_Cpx_Proof {

        private final RNTDecisionProcedure.Verdict verdict;
        private final boolean basic;
        private final boolean sizeBoundedTerms;
        private final boolean packingSymbol;
        private final RewriteStrategy strategy;
        private final ComplexityYNM value;

        DecidableRNTCpxProof(final RNTDecisionProcedure.Verdict verdict,
            final boolean basic,
            final boolean sizeBoundedTerms,
            final boolean packingSymbol,
            final RewriteStrategy strategy,
            final ComplexityYNM value) {
            this.verdict = verdict;
            this.basic = basic;
            this.sizeBoundedTerms = sizeBoundedTerms;
            this.packingSymbol = packingSymbol;
            this.strategy = strategy;
            this.value = value;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder s = new StringBuilder();
            s.append(this.verdict.export(o));
            s.append(o.paragraph());
            s.append(this.verdict.exportRuntime(o));
            s.append(o.paragraph());
            if (this.verdict.sast) {
                if (this.basic) {
                    s.append(o.export("Every basic term contains exactly one defined symbol, so the expected runtime complexity is at most "
                        + this.verdict.eMaxCeiling()
                        + ", i.e., in O(1)."));
                } else if (this.sizeBoundedTerms) {
                    s.append(o.export("All defined symbols are constants and no symbol has an arity > 1, so every term contains at most one "
                        + "defined symbol and the expected derivational complexity is at most "
                        + this.verdict.eMaxCeiling()
                        + ", i.e., in O(1)."));
                } else {
                    s.append(o.export("As |pos_D(t)| <= |t|, the expected derivational complexity is in O(n)."));
                    if (this.packingSymbol) {
                        s.append(o.export(" It is also in Omega(n), since a symbol of arity > 1 yields terms of size n with Omega(n) parallel "
                            + "redexes with constructor arguments, which all have to be rewritten."));
                    }
                }
            } else {
                s.append(o.export("So the expected " + (this.basic ? "runtime" : "derivational")
                    + " complexity is infinite for all n >= "
                    + this.verdict.witnessInstance.getSize()
                    + "."));
            }
            if (this.strategy != RewriteStrategy.FULL) {
                s.append(o.paragraph());
                s.append(o.export("The bounds also hold for " + this.strategy.getRepresentation()
                    + " rewriting, as all rewrite trees used "
                    + "above only rewrite parallel redexes whose arguments are normal forms."));
            }
            s.append(o.paragraph());
            s.append(o.export("Resulting bounds: " + this.value.toWstString()));
            return s.toString();
        }
    }
}
