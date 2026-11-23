package aprove.verification.probabilistic.Termination.PTRSProblem.SAST.Processors;

import java.math.*;
import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.Solvers.*;
import aprove.verification.dpframework.Orders.Utility.POLO.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;

/**
 * Processor that tries to order the rules of a PTRS
 * directly using polynomial interpretations.
 * Uses the orderings to prove SAST from [ADY19].
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class PTRS_SAST_DirectPoloProcessor extends PTRS_SAST_ProblemProcessor {

    // ================================================================================
    // Properties
    // ================================================================================

    private final boolean allstrict;

    private final SolverFactory order;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    @ParamsViaArgumentObject
    public PTRS_SAST_DirectPoloProcessor(final Arguments arguments) {
        this.allstrict = arguments.allstrict;
        this.order = arguments.order;
    }

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isPTRSApplicable(final PTRSProblem obl) {
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result processPTRSProblem(final PTRSProblem ptrs, final Abortion aborter)
        throws AbortionException {

        final Set<ProbabilisticRule> toOrderRules = new HashSet<>();

        toOrderRules.addAll(ptrs.getPR());

        final List<ExportableOrder<TRSTerm>> orderList = new ArrayList<>();
        final List<Set<ProbabilisticRule>> removedRulesList = new ArrayList<>();

        while (!toOrderRules.isEmpty()) {
            final POLO order = findOrdering(ptrs, this.allstrict, aborter);

            if (order == null) {
                return ResultFactory.unsuccessful("Could not find a suitable poly interpretation");
            }

            /* find strict tuples */
            final Set<ProbabilisticRule> removedRules = new HashSet<>();

            for (final ProbabilisticRule rule : toOrderRules) {
                if (checkStrictDecrease(rule, order, aborter)) {
                    removedRules.add(rule);
                }
            }
            toOrderRules.removeAll(removedRules);

            orderList.add(order);
            removedRulesList.add(removedRules);
        }

        final SASTDirectPoloPTRSProof POLOproof = new SASTDirectPoloPTRSProof(orderList, ptrs, removedRulesList);

        return ResultFactory.proved(POLOproof);
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
    private POLO findOrdering(final PTRSProblem ptrs, final boolean allstrict, final Abortion aborter)
        throws AbortionException {

        final POLOSolver solver = this.order.getMLPOLOSolver(ptrs.getSignature(), aborter);

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
    private Formula<Diophantine> createFormula(final PTRSProblem ptrs,
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

        final List<Formula<Diophantine>> finalConstraintsList = new ArrayList<>();
        finalConstraintsList.add(expectedValueConstraintFormula);
        finalConstraintsList.add(monotonicityFormula);
        final Formula<Diophantine> finalFormula = ff.buildAnd(finalConstraintsList);

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

    /**
     * @param rule - the probabilistic rewrite rule for this formula
     * @param order - the polynomial interpretation that solved the RPP formula
     * @param aborter - Aborter to check the timer
     * @return true, if the rule together with the polynomial interpretation stored in order satisfies the "strictly decreasing" formula
     */
    private boolean checkStrictDecrease(final ProbabilisticRule rule, final POLO order, final Abortion aborter) {
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
                    order.getInterpretation().interpretTerm(term, aborter).times(SimplePolynomial.create(multipliesProb)));
            }
        }

        final VarPolynomial lhsPoly = (order.getInterpretation().interpretTerm(rule.getLeft(), aborter)).times(SimplePolynomial.create(multiplier));
        final VarPolynomial constraint = lhsPoly.minus(rhsExpectedPoly);
        final VarPolyConstraint termConstraint = new VarPolyConstraint(constraint, ConstraintType.GT);
        if (termConstraint.isValid()) {
            return true;
        } else {
            return false;
        }
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class SASTDirectPoloPTRSProof extends Proof.DefaultProof {

        private final List<ExportableOrder<TRSTerm>> orderList;
        private final List<Set<ProbabilisticRule>> removedRulesList;

        SASTDirectPoloPTRSProof(final List<ExportableOrder<TRSTerm>> orderList,
            final PTRSProblem origPTRS,
            final List<Set<ProbabilisticRule>> removedRulesList) {
            this.orderList = orderList;
            this.removedRulesList = removedRulesList;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            result.append(o.paragraph());
            result.append("We use the direct application of polynomial interpretations " + o.cite(new Citation[] { Citation.ADY19, Citation.KASSING_DISS }) + ".");
            result.append(o.linebreak());
            for (int i = 0; i < this.orderList.size(); i++) {
                result.append("We can order the following rules strictly: ");
                result.append(o.linebreak());
                for (final ProbabilisticRule rule : this.removedRulesList.get(i)) {
                    result.append(rule.export(o));
                }
                result.append(o.linebreak());
                result.append("Using the following Interpretation: ");
                result.append(o.linebreak());
                result.append(this.orderList.get(i).export(o));
            }

            return result.toString();
        }
    }

    // ================================================================================
    // Arguments Class
    // ================================================================================

    public static class Arguments {

        public SolverFactory order;
        public boolean allstrict = true;
    }

}
