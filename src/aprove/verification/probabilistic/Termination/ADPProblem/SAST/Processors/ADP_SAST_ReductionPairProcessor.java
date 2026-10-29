package aprove.verification.probabilistic.Termination.ADPProblem.SAST.Processors;

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
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.ADPProblem.SAST.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import immutables.*;

/**
 * Reduction Pair Processor as described in Leon's master's thesis
 * (Analyzing Strong Almost-Sure Termination for Probabilistic Term Rewriting Using Dependency Pairs, 2025)
 *
 * @author J-C Kassing & Leon Spitzer
 * @version $Id$
 */
public class ADP_SAST_ReductionPairProcessor extends ADP_SAST_ProblemProcessor {

    // ================================================================================
    // Properties
    // ================================================================================

    private final boolean allstrict;
    private final SolverFactory order;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    @ParamsViaArgumentObject
    public ADP_SAST_ReductionPairProcessor(final Arguments arguments) {
        this.allstrict = arguments.allstrict;
        this.order = arguments.order;
    }

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isSAST_ADPApplicable(final ADP_SAST_Problem qdp) {
        // Only applies if we restrict to innermost evaluation and basic start terms
        if (!qdp.getInnermost() || !qdp.isBasic()) {
            return false;
        }
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result processSAST_ADPProblem(final ADP_SAST_Problem oriqSast_ADP, final Abortion aborter) throws AbortionException {

        /* Find ordering with interpretation such that:
         *
         *  1. The expected value of all usable rules must be weakly decreasing when removing annotations.
         *  2. All rules must be weakly decreasing when comparing the annotated left-hand side with
         *     the expected value of all annotated subterms (sum) in the right-hand side.
         *  3. There is at least one ADP who is strictly decreasing comparing the annotated left-hand side with the
         *     expected value of all annotated subterms (sum) in the right-hand side.
         *
         *  We move the rules that fulfil 3. from S to K.
         */

        final POLO order = findOrdering(oriqSast_ADP, this.allstrict, aborter);

        if (order == null) {
            return ResultFactory.unsuccessful("Could not find a suitable poly interpretation");
        }

        final Set<ProbabilisticRule> keptDepTuples = new HashSet<>();
        final Set<ProbabilisticRule> removedDepTuples = new HashSet<>();
        final ImmutableSet<ProbabilisticRule> oldRules = ImmutableCreator.create(oriqSast_ADP.getSWithQ());
        final Set<ProbabilisticRule> newSadps = new HashSet<>();

        // Create copy of S and K
        for (final ProbabilisticRule rule : oriqSast_ADP.getS()) {
            newSadps.add(rule);
        }

        final Set<ProbabilisticRule> newKadps = new HashSet<>();
        for (final ProbabilisticRule rule : oriqSast_ADP.getK()) {
            newKadps.add(rule);
        }

        /* find strict dep tuples */
        final Set<ProbabilisticRule> oldDepTuples = oriqSast_ADP.getPwithOnlyAnno();
        for (final ProbabilisticRule depTuple : oldDepTuples) {
            if (!checkStrictDecrease(depTuple, oriqSast_ADP, order, aborter)) {
                keptDepTuples.add(depTuple);
            } else {
                removedDepTuples.add(depTuple);
                // Move strict decreasing tuples from S to K
                newSadps.remove(depTuple);
                newKadps.add(depTuple);
            }
        }

        // No dependency tuple could be oriented strictly: the processor made no progress.
        if (removedDepTuples.isEmpty()) {
            return ResultFactory.unsuccessful("Reduction pair oriented no dependency tuple strictly; no progress");
        }

        final PQTRSProblem newpqtrs =
            PQTRSProblem.create(oldRules, oriqSast_ADP.getQ(), oriqSast_ADP.getStrat(), ProbabilisticTerminationResult.SAST, oriqSast_ADP.isBasic());
        final ADP_SAST_Problem newpqdp = ADP_SAST_Problem.create(oriqSast_ADP
            .getP(), newSadps, newKadps, newpqtrs, oriqSast_ADP.getReachPQTRS(), oriqSast_ADP.getStrat(), oriqSast_ADP.isBasic(), oriqSast_ADP.getBiAnnoMap());

        final SAST_ADPReductionPairProof RPPproof = new SAST_ADPReductionPairProof(order,
            oriqSast_ADP,
            newpqdp,
            removedDepTuples,
            keptDepTuples);

        return ResultFactory.proved(newpqdp, YNMImplication.EQUIVALENT, RPPproof);
    }

    /**
     * The SMT-Solving part of the processor.
     * This includes the creation of an interpretation, the formula about diophantine constraints
     * and the search for a satisfying interpretation via some solver.
     *
     * @param Sast_ADPProblem - the original PQDPProblem problem
     * @param allstrict - boolean whether we want to strict all of the rules strictly
     * @param aborter - Aborter to check the timer
     * @return the satisfying polynomial interpretation
     * @throws AbortionException
     */
    private POLO findOrdering(final ADP_SAST_Problem sast_ADPProblem, final boolean allstrict, final Abortion aborter)
        throws AbortionException {

        final POLOSolver solver = this.order.getMLPOLOSolver(sast_ADPProblem.getSignature(), aborter);
        solver.setAllowWeakMonotonicity(true);

        final Formula<Diophantine> fml = createFormula(sast_ADPProblem, solver.getInterpretation(), aborter);

        return solver.solveDioFormula(fml, aborter);
    }

    /**
     * Create the formula that we need to satisfy
     *  1. All expected values are non increasing,
     *  2. The expected value of the terms with annotation (sum) of the rhs needs to strictly decrease
     *
     * @param sast_ADPProblem - the original PQDPProblem problem
     * @param interpretation - the polynomial interpretation with variables as coefficients
     * @param aborter - Aborter to check the timer
     * @return The complete formula for the probabilistic RPP
     */
    private Formula<Diophantine> createFormula(final ADP_SAST_Problem sast_ADPProblem,
        final Interpretation interpretation,
        final Abortion aborter) {

        final FormulaFactory<Diophantine> ff = NonCountingCircuitFactory.create(SplitMode.FLATTEN, SplitMode.LEFT_COMB); //TODO: Check these parameters

        final Set<ProbabilisticRule> depTuples = sast_ADPProblem.getSwithOnlyAnno();
        final Set<ProbabilisticRule> probRules = sast_ADPProblem.getSWithQ();

        // Create the Formula of Constraints that we want to solve:
        // 1. The expected value is non-increasing for every dependency tuple and every rewrite rule
        final List<Formula<Diophantine>> expectedValueConstraintList = new ArrayList<>();
        for (final ProbabilisticRule probRule : probRules) {
            expectedValueConstraintList.add(createRuleFormulaExpectation(ff, probRule, interpretation, aborter));
        }
        for (final ProbabilisticRule depTuple : depTuples) {
            expectedValueConstraintList.add(createDepTupleFormulaExpectation(ff, depTuple, interpretation, sast_ADPProblem, aborter));
        }
        final Formula<Diophantine> expectedValueConstraintFormula = ff.buildAnd(expectedValueConstraintList);

        // 2. The expected value of the terms with annotation (sum) of the rhs needs to strictly decrease
        final List<Formula<Diophantine>> removalConstraintList = new ArrayList<>();
        for (final ProbabilisticRule depTuple : depTuples) {
            removalConstraintList.add(createDepTupleStrictFormulaExpectation(ff, depTuple, interpretation, sast_ADPProblem, aborter));
        }

        Formula<Diophantine> removalConstraintFormula;
        if (this.allstrict) {
            removalConstraintFormula = ff.buildAnd(removalConstraintList);
        } else {
            removalConstraintFormula = ff.buildOr(removalConstraintList);
        }

        final List<Formula<Diophantine>> finalConstraintsList = new ArrayList<>();
        finalConstraintsList.add(expectedValueConstraintFormula);
        finalConstraintsList.add(removalConstraintFormula);
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
            final Integer amount = entry.getValue(); // amount??

            final BigInteger multipliesProb = prob.multiply(multiplier).reduce().getNumerator();

            for (int i = 0; i < amount; i++) {
                rhsExpectedPoly = rhsExpectedPoly.plus(
                    interpretation.interpretTerm(term, aborter).times(SimplePolynomial.create(multipliesProb)));
            }
        }

        final VarPolynomial lhsPoly = (interpretation.interpretTerm(rule.getLeft(), aborter))
            .times(SimplePolynomial.create(multiplier));
        final VarPolynomial constraint = lhsPoly.minus(rhsExpectedPoly);
        final Set<SimplePolyConstraint> simplePolyConstraintSet = new VarPolyConstraint(constraint, ConstraintType.GE)
            .createCoefficientConstraints();
        final List<Formula<Diophantine>> ruleFormulaList = new ArrayList<>();
        for (final SimplePolyConstraint spc : simplePolyConstraintSet) {
            final Formula<Diophantine> helpFormula = ff.buildTheoryAtom(Diophantine.create(spc));
            ruleFormulaList.add(helpFormula);
        }
        return ff.buildAnd(ruleFormulaList);
    }

    /**
     * @param ff - FormulaFactory for formulas about Diophantine constraints
     * @param rule - the probabilistic dependency tuple for this formula
     * @param interpretation - the polynomial interpretation with variables as coefficients
     * @param aborter - Aborter to check the timer
     * @return formula to encode "expectation non-increasing"
     */
    private Formula<Diophantine> createDepTupleFormulaExpectation(final FormulaFactory<Diophantine> ff,
        final ProbabilisticRule rule,
        final Interpretation interpretation,
        final ADP_SAST_Problem sast_ADPProblem,
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

            VarPolynomial setPoly = VarPolynomial.ZERO;

            for (final Pair<TRSFunctionApplication, Position> annoSubterm : term.getAnnoSubtermsWithPositions(sast_ADPProblem.getDeAnnoMap())) {
                setPoly = setPoly.plus(interpretation.interpretTerm(annoSubterm.x, aborter));
            }

            for (int i = 0; i < amount; i++) {
                rhsExpectedPoly = rhsExpectedPoly.plus(setPoly.times(SimplePolynomial.create(multipliesProb)));
            }
        }

        final VarPolynomial lhsPoly = (interpretation.interpretTerm(rule.getLeft(), aborter))
            .times(SimplePolynomial.create(multiplier));
        final VarPolynomial constraint = lhsPoly.minus(rhsExpectedPoly);
        final Set<SimplePolyConstraint> simplePolyConstraintSet = new VarPolyConstraint(constraint, ConstraintType.GE)
            .createCoefficientConstraints();
        final List<Formula<Diophantine>> ruleFormulaList = new ArrayList<>();
        for (final SimplePolyConstraint spc : simplePolyConstraintSet) {
            final Formula<Diophantine> helpFormula = ff.buildTheoryAtom(Diophantine.create(spc));
            ruleFormulaList.add(helpFormula);
        }
        return ff.buildAnd(ruleFormulaList);
    }

    /**
     * @param ff - FormulaFactory for formulas about Diophantine constraints
     * @param rule - the probabilistic dependency tuple for this formula
     * @param interpretation - the polynomial interpretation with variables as coefficients
     * @param aborter - Aborter to check the timer
     * @return formula to encode "expectation dep tuple decreasing"
     */
    private Formula<Diophantine> createDepTupleStrictFormulaExpectation(final FormulaFactory<Diophantine> ff,
        final ProbabilisticRule rule,
        final Interpretation interpretation,
        final ADP_SAST_Problem sast_ADPProblem,
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

            VarPolynomial setPoly = VarPolynomial.ZERO;

            for (final Pair<TRSFunctionApplication, Position> annoSubterm : term.getAnnoSubtermsWithPositions(sast_ADPProblem.getDeAnnoMap())) {
                setPoly = setPoly.plus(interpretation.interpretTerm(annoSubterm.x, aborter));
            }

            for (int i = 0; i < amount; i++) {
                rhsExpectedPoly = rhsExpectedPoly.plus(setPoly.times(SimplePolynomial.create(multipliesProb)));
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
     * @return true, if the rule together with the polynomial interpretation stored in order satisfies the 3. "strictly decreasing" formula
     */
    private boolean checkStrictDecrease(final ProbabilisticRule rule, final ADP_SAST_Problem sast_ADPProblem, final POLO order, final Abortion aborter) {
        VarPolynomial rhsExpectedPoly = VarPolynomial.ZERO;

        // Compute a multiplier such that we are dealing with natural coefficients (LCM of the denominators),
        // and weight each outcome by its probability -- exactly as createDepTupleStrictFormulaExpectation does,
        // so that this re-check accepts precisely the strict decreases the solver was asked to satisfy.
        BigInteger multiplier = BigInteger.ONE;
        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
            final BigFraction prob = entry.getKey().getValue();
            multiplier = multiplier.multiply(prob.getDenominator());
        }

        // l -> {p1 : r1, ..., pk : rk}: rhs expected value = sum_i amount_i * p_i * (annotated subterms of r_i)
        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
            final TRSTerm term = entry.getKey().getKey();
            final BigFraction prob = entry.getKey().getValue();
            final Integer amount = entry.getValue();

            final BigInteger multipliesProb = prob.multiply(multiplier).reduce().getNumerator();

            // Adding all annotated subterms interpretations to setPoly
            VarPolynomial setPoly = VarPolynomial.ZERO;
            for (final Pair<TRSFunctionApplication, Position> annoSubterm : term.getAnnoSubtermsWithPositions(sast_ADPProblem.getDeAnnoMap())) {
                setPoly = setPoly.plus(order.getInterpretation().interpretTerm(annoSubterm.x, aborter));
            }

            for (int i = 0; i < amount; i++) {
                rhsExpectedPoly = rhsExpectedPoly.plus(setPoly.times(SimplePolynomial.create(multipliesProb)));
            }
        }

        // Multiply the lhs by the same multiplier to compare with the probability-weighted expected value.
        final VarPolynomial lhsTuplePoly =
            order.getInterpretation().interpretTerm(rule.getLeft(), aborter).times(SimplePolynomial.create(multiplier));

        // Make sure that that the expected Tuple part is strictly smaller
        final VarPolynomial tupleConstraintPoly = lhsTuplePoly.minus(rhsExpectedPoly);
        final VarPolyConstraint tupleConstraint = new VarPolyConstraint(tupleConstraintPoly, ConstraintType.GT);
        if (tupleConstraint.isValid()) {
            return true;
        }
        return false;
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class SAST_ADPReductionPairProof extends Proof.DefaultProof {

        private final ExportableOrder<TRSTerm> order;
        private final ADP_SAST_Problem origPQDP;
        private final Set<ProbabilisticRule> orientedPRules;
        private final Set<ProbabilisticRule> keptPRules;

        SAST_ADPReductionPairProof(final ExportableOrder<TRSTerm> order,
            final ADP_SAST_Problem origqdp,
            final ADP_SAST_Problem resultingQDP,
            final Set<ProbabilisticRule> orientedPRules,
            final Set<ProbabilisticRule> keptPRules) {
            this.order = order;
            this.origPQDP = origqdp;
            this.orientedPRules = orientedPRules;
            this.keptPRules = keptPRules;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            result.append(o.paragraph());
            if (this.origPQDP.getInnermost()) {
                result.append("We use the reduction pair processor " + "(Leon's master's thesis)" + ".");
            } else { //full SAST
                result.append("We use the reduction pair processor " + " (!PROTOTYPE!) " + ".");
            }
            result.append(o.linebreak());
            result.append("The following pairs can be oriented strictly and are moved from S to K:");
            result.append(o.cond_linebreak());
            result.append(o.set(this.orientedPRules, Export_Util.RULES));
            result.append(o.cond_linebreak());
            result.append("The remaining pairs can at least be oriented weakly:");
            result.append(o.cond_linebreak());
            result.append(o.set(this.keptPRules, Export_Util.RULES));
            result.append(o.cond_linebreak());
            result.append("Used ordering:  ");
            result.append(this.order.export(o));

            return result.toString();
        }
    }

    // ================================================================================
    // Arguments Class
    // ================================================================================

    public static class Arguments {

        public boolean allstrict = false;
        public SolverFactory order;
    }

}
