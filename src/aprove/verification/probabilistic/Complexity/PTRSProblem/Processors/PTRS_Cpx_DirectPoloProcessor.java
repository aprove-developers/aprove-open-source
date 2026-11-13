package aprove.verification.probabilistic.Complexity.PTRSProblem.Processors;

import java.math.*;
import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Complexity.PTRSProblem.*;
import aprove.verification.probabilistic.Termination.ADPProblem.SAST.*;

/**
 * Processor that tries to order the rules of a PTRS
 * directly using polynomial interpretations.
 * Uses the orderings to prove SAST from [ADY19].
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class PTRS_Cpx_DirectPoloProcessor extends PTRS_Cpx_Processor {

    // ================================================================================
    // Properties
    // ================================================================================

    private final boolean allstrict;
    private final boolean constant;
    private final boolean exponential;
    private final SolverFactory order;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    @ParamsViaArgumentObject
    public PTRS_Cpx_DirectPoloProcessor(final Arguments arguments) {
        this.allstrict = arguments.allstrict;
        this.constant = arguments.constant;
        this.exponential = arguments.exponential;
        this.order = arguments.order;
    }

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isCpxPTRSApplicable(final PTRS_Cpx_Problem obl) {
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result processCpxPTRS(final PTRS_Cpx_Problem ptrs, final Abortion aborter)
        throws AbortionException {

        final Set<ProbabilisticRule> toOrderRules = new HashSet<>();

        toOrderRules.addAll(ptrs.getPR());

        new ArrayList<>();
        final List<Set<ProbabilisticRule>> removedRulesList = new ArrayList<>();

        final POLO order = findOrdering(ptrs, this.allstrict, aborter);

        if (order == null) {
            return ResultFactory.unsuccessful("Could not find a suitable poly interpretation");
        }

        ComplexityValue upperBound;

        if (ptrs.isBasic()) {
            if (!this.exponential) {
                upperBound = ComplexityValue.fixedDegreePoly(order.getInterpretation().getDegree(ptrs.getDefSymbolsOfR()));
            } else if (order.getInterpretation().getDegree() == 1) {
                upperBound = ComplexityValue.exponential();
            } else {
                upperBound = ComplexityValue.doubleExponential();
            }
        } else {
            if (order.getInterpretation().getDegree() == 0) {
                upperBound = ComplexityValue.constant();
            } else if (!this.exponential && order.getInterpretation().getDegree() == 1) {
                upperBound = ComplexityValue.fixedDegreePoly(1);
            } else if (order.getInterpretation().getDegree() == 1) {
                upperBound = ComplexityValue.exponential();
            } else {
                upperBound = ComplexityValue.doubleExponential();
            }
        }

        final CpxPTRS_DirectPoloProof POLOproof = new CpxPTRS_DirectPoloProof(upperBound, order, ptrs, removedRulesList);

        return ResultFactory.provedWithValue(ComplexityYNM.createUpper(upperBound), POLOproof);
    }

    /**
     * The SMT-Solving part of the processor.
     * This includes the creation of an interpretation, the formula about Diophantine constraints
     * and the search for a satisfying interpretation via some solver.
     *
     * @param pqdpProblem - the original PQDPProblem problem
     * @param allstrict - boolean whether we want to strict all of the rules strictly
     * @param aborter - Aborter to check the timer
     * @return the satisfying polynomial interpretation
     * @throws AbortionException
     */
    private POLO findOrdering(final PTRS_Cpx_Problem ptrs, final boolean allstrict, final Abortion aborter)
        throws AbortionException {

        final POLOSolver solver = this.order.getCPIMLPOLOSolver(ptrs.getDefSymbolsOfR(), ptrs.getConstSymbolsOfR(), aborter);

        final Formula<Diophantine> fml = createFormula(ptrs, solver.getInterpretation(), aborter);

        return solver.solveDioFormula(fml, aborter);
    }

    /**
     * Create the formula that we need to satisfy
     * (All expected values are non increasing, at least one element in the support of the rhs is strictly decreasing)
     *
     * @param pqdpProblem - the original PQDPProblem problem
     * @param interpretation - the polynomial interpretation with variables as coefficients
     * @param aborter - Aborter to check the timer
     * @return The complete formula for the probabilistic RPP
     */
    private Formula<Diophantine> createFormula(final PTRS_Cpx_Problem ptrs,
        final Interpretation interpretation,
        final Abortion aborter) {

        final FormulaFactory<Diophantine> ff = NonCountingCircuitFactory.create(SplitMode.FLATTEN, SplitMode.LEFT_COMB); //TODO: Check these parameters

        final Set<ProbabilisticRule> probRules = ptrs.getPR();

        //Create the Formula of Constraints that we want to solve:
        //1. The expected value is strictly decreasing for every rewrite rule
        final List<Formula<Diophantine>> expectedValueConstraintList = new ArrayList<>();
        for (final ProbabilisticRule probRule : probRules) {
            expectedValueConstraintList.add(createRuleFormulaExpectation(ff, probRule, interpretation, aborter));
        }
        Formula<Diophantine> expectedValueConstraintFormula;
        if (this.allstrict) {
            expectedValueConstraintFormula = ff.buildAnd(expectedValueConstraintList);
        } else {
            expectedValueConstraintFormula = ff.buildOr(expectedValueConstraintList);
        }

        //3. Add monotonicity constraints
        final Set<SimplePolyConstraint> monotonicityConstraint =
            interpretation.getStrongMonotonicityConstraints(null);

        final List<Formula<Diophantine>> monotonicityFormulaList = new ArrayList<>();

        for (final SimplePolyConstraint spc : monotonicityConstraint) {
            final Formula<Diophantine> helpFormula = ff.buildTheoryAtom(Diophantine.create(spc));
            monotonicityFormulaList.add(helpFormula);
        }
        final Formula<Diophantine> monotonicityFormula = ff.buildAnd(monotonicityFormulaList);

        //4. Add CPI Constraints
        final Formula<Diophantine> cpiFormula = createCPIConstraintsFormula(ff, ptrs, interpretation, aborter);

        final List<Formula<Diophantine>> finalConstraintsList = new ArrayList<>();
        finalConstraintsList.add(expectedValueConstraintFormula);
        finalConstraintsList.add(monotonicityFormula);
        finalConstraintsList.add(cpiFormula);
        final Formula<Diophantine> finalFormula = ff.buildAnd(finalConstraintsList);

        return finalFormula;

    }

    /**
     * @param f - a function symbol that has a linear interpretation in this
     * @return a Diophantine constraint whose satisfaction by a Diophantine
     *  model entails that the interpretation of f is a CPI, i.e.,
     *  Pol(f) = a_1 * x_1 + ... + a_k * x_k + b with a_i in {0,1}
     */
    public Formula<Diophantine> createCPIConstraintsFormula(final FormulaFactory<Diophantine> ff,
        final ADP_SAST_Problem sast_ADPProblem,
        final Interpretation interpretation,
        final Abortion aborter) {

        final Set<FunctionSymbol> constructorSig = new LinkedHashSet<>(sast_ADPProblem.getSignature());
        final Set<FunctionSymbol> definedSig = sast_ADPProblem.getSwithQ().getDefSymbolsOfR();
        constructorSig.removeAll(definedSig);

        final List<Formula<Diophantine>> resultFormulaList = new ArrayList<>();

        for (final FunctionSymbol f : constructorSig) {
            for (int i = 0; i < f.getArity(); i++) {
                final Formula<Diophantine> helpFormula = ff.buildTheoryAtom(interpretation.getCPIConstraintForLinearInterpretation(f, i));
                resultFormulaList.add(helpFormula);
            }
        }
        final Formula<Diophantine> finalFormula = ff.buildAnd(resultFormulaList);
        return finalFormula;
    }

    /**
     * @param f - a function symbol that has a linear interpretation in this
     * @return a Diophantine constraint whose satisfaction by a Diophantine
     *  model entails that the interpretation of f is a CPI, i.e.,
     *  Pol(f) = a_1 * x_1 + ... + a_k * x_k + b with a_i in {0,1}
     */
    public Formula<Diophantine> createCPIConstraintsFormula(final FormulaFactory<Diophantine> ff,
        final PTRS_Cpx_Problem ptrs,
        final Interpretation interpretation,
        final Abortion aborter) {

        final Set<FunctionSymbol> constructorSig = new LinkedHashSet<>(ptrs.getSignature());
        final Set<FunctionSymbol> definedSig = ptrs.getDefSymbolsOfR();
        constructorSig.removeAll(definedSig);

        final List<Formula<Diophantine>> resultFormulaList = new ArrayList<>();

        if (!this.exponential) {
            if (ptrs.isBasic()) {
                for (final FunctionSymbol f : constructorSig) {
                    for (int i = 0; i < f.getArity(); i++) {
                        final Formula<Diophantine> helpFormula = ff.buildTheoryAtom(interpretation.getCPIConstraintForLinearInterpretation(f, i));
                        resultFormulaList.add(helpFormula);
                    }
                }
            } else {
                for (final FunctionSymbol f : ptrs.getSignature()) {
                    for (int i = 0; i < f.getArity(); i++) {
                        final Formula<Diophantine> helpFormula = ff.buildTheoryAtom(interpretation.getCPIConstraintForLinearInterpretation(f, i));
                        resultFormulaList.add(helpFormula);
                    }
                }
            }
        }

        if (this.constant) {
            for (final FunctionSymbol f : ptrs.getSignature()) {
                for (int i = 0; i < f.getArity(); i++) {
                    final Formula<Diophantine> helpFormula = ff.buildTheoryAtom(interpretation.getConstantConstraintForLinearInterpretation(f, i));
                    resultFormulaList.add(helpFormula);
                }
            }
        }

        final Formula<Diophantine> finalFormula = ff.buildAnd(resultFormulaList);
        return finalFormula;
    }

    /**
     * @param ff - FormulaFactory for formulas about Diophantine constraints
     * @param rule - the probabilistic rewrite rule for this formula
     * @param interpretation - the polynomial interpretation with variables as coefficients
     * @param aborter - Aborter to check the timer
     * @return formula to encode "expectation non-increasing"
     */
    private Formula<Diophantine> createRuleFormulaExpectation(final FormulaFactory<Diophantine> ff,
        final ProbabilisticRule rule,
        final Interpretation interpretation,
        final Abortion aborter) {
        VarPolynomial rhsExpectedPoly = VarPolynomial.ZERO;

        //Compute a multiplier such that we are dealing with simple polys at the end with natural coefficients
        BigInteger multiplier = BigInteger.ONE;
        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
            final BigFraction prob = entry.getKey().getValue();
            multiplier = multiplier.multiply(prob.getDenominator());
        }

        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
            final TRSTerm term = entry.getKey().getKey();
            final BigFraction prob = entry.getKey().getValue();
            final Integer amount = entry.getValue();

            final BigInteger multipliesProb = prob.multiply(multiplier).reduce().getNumerator();

            for (int i = 0; i < amount; i++) {
                rhsExpectedPoly = rhsExpectedPoly.plus(
                    interpretation.interpretTerm(term, aborter).times(SimplePolynomial.create(multipliesProb)));
            }
        }

        final VarPolynomial lhsPoly = (interpretation.interpretTerm(rule.getLeft(), aborter))
            .times(SimplePolynomial.create(multiplier));
        final VarPolynomial constraint = lhsPoly.minus(rhsExpectedPoly);
        final Set<SimplePolyConstraint> simplePolyConstraintSet = new VarPolyConstraint(constraint, ConstraintType.GT)
            .createCoefficientConstraints();
        final List<Formula<Diophantine>> ruleFormulaList = new ArrayList<>();
        for (final SimplePolyConstraint spc : simplePolyConstraintSet) {
            final Formula<Diophantine> helpFormula = ff.buildTheoryAtom(Diophantine.create(spc));
            ruleFormulaList.add(helpFormula);
        }
        return ff.buildAnd(ruleFormulaList);
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class CpxPTRS_DirectPoloProof extends Proof.DefaultProof {

        private final ComplexityValue resultComplexity;
        private final ExportableOrder<TRSTerm> order;

        CpxPTRS_DirectPoloProof(final ComplexityValue resultComplexity,
            final ExportableOrder<TRSTerm> order,
            final PTRS_Cpx_Problem origPTRS,
            final List<Set<ProbabilisticRule>> removedRulesList) {
            this.resultComplexity = resultComplexity;
            this.order = order;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            result.append(o.paragraph());
            result.append("We use the direct application of polynomial interpretations " + o.cite(new Citation[] { Citation.ADY19, Citation.KASSING_DISS }) + ".");
            result.append(o.linebreak());
            result.append("Using the following Interpretation: ");
            result.append(o.linebreak());
            result.append("Resulting in the following upper complexity bound: ");
            result.append(this.resultComplexity.export(o));
            result.append(this.order.export(o));

            return result.toString();
        }
    }

    // ================================================================================
    // Arguments Class
    // ================================================================================

    public static class Arguments {

        public SolverFactory order;
        public boolean constant = false;
        public boolean exponential = false;
        public boolean allstrict = true;
    }

}
