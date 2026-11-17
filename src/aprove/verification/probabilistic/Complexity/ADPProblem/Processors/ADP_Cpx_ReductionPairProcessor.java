package aprove.verification.probabilistic.Complexity.ADPProblem.Processors;

import java.math.*;
import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.Implications.*;
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
import aprove.verification.probabilistic.Complexity.ADPProblem.*;
import aprove.verification.probabilistic.Complexity.PTRSProblem.*;
import immutables.*;

/**
 * Reduction Pair Processor as described in Leon's master's thesis
 * (Analyzing Strong Almost-Sure Termination for Probabilistic Term Rewriting Using Dependency Pairs, 2025)
 *
 * @author J-C Kassing & Leon Spitzer
 * @version $Id$
 */
public class ADP_Cpx_ReductionPairProcessor extends ADP_Cpx_ProblemProcessor {

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
    public ADP_Cpx_ReductionPairProcessor(final Arguments arguments) {
        this.allstrict = arguments.allstrict;
        this.constant = arguments.constant;
        this.exponential = arguments.exponential;
        this.order = arguments.order;
    }

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isCpxADP_Applicable(final ADP_Cpx_Problem qdp) {
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
    public Result processCpxADPProblem(final ADP_Cpx_Problem oriqSast_ADP, final Abortion aborter) throws AbortionException {

        /* Find ordering with interpretation such that:
         *
         *  1. The expected value of all usable rules must be weakly decreasing when removing annotations.
         *  2. All rules must be weakly decreasing when comparing the annotated left-hand side with
         *     the expected value of all annotated subterms (sum) in the right-hand side.
         *  3. There is at least one ADP who is strictly decreasing comparing the annotated left-hand side with the
         *     expected value of all annotated subterms (sum) in the right-hand side.
         *
         *  We move the rules that fulfill 3. from S to K.
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

        final PQTRS_Cpx_Problem newpqtrs = PQTRS_Cpx_Problem.create(oldRules, oriqSast_ADP.getQ(), oriqSast_ADP.getStrat(), oriqSast_ADP.isBasic());
        final ADP_Cpx_Problem newpqdp = ADP_Cpx_Problem
            .create(oriqSast_ADP.getP(), newSadps, newKadps, newpqtrs, oriqSast_ADP.getStrat(), oriqSast_ADP.isBasic(), oriqSast_ADP.getBiAnnoMap());

        ComplexityValue upperBound;

        if (!this.exponential) {
            upperBound = ComplexityValue.fixedDegreePoly(order.getInterpretation().getDegree(oriqSast_ADP.getAnnoFunctionSymbols()));
        } else if (order.getInterpretation().getDegree() == 1) { //nur Konstruktoren
            upperBound = ComplexityValue.exponential();
        } else {
            upperBound = ComplexityValue.doubleExponential();
        }

        final CpxADP_ReductionPairProof rpProof = new CpxADP_ReductionPairProof(upperBound,
            order,
            oriqSast_ADP,
            newpqdp,
            removedDepTuples,
            keptDepTuples);

        return ResultFactory.proved(
            newpqdp,
            UpperBound.create(new SumComputation(upperBound)),
            rpProof);

    }

    /**
     * The constraints also interpret the de-annotated versions of the annotated symbols. Such a symbol does not
     * occur in the problem anymore if all of its rules and all of its unannotated occurrences have been removed.
     * If it is not defined anymore, then it is treated as a constructor.
     */
    private static Set<FunctionSymbol> getSignatureWithDeAnnoSymbols(final ADP_Cpx_Problem CpxADPProblem) {
        final Set<FunctionSymbol> signature = new LinkedHashSet<>(CpxADPProblem.getSignature());
        for (final FunctionSymbol f : CpxADPProblem.getSignature()) {
            final FunctionSymbol deAnno = CpxADPProblem.getDeAnnoMap().get(f);
            if (deAnno != null) {
                signature.add(deAnno);
            }
        }
        return signature;
    }

    /**
     * The SMT-Solving part of the processor.
     * This includes the creation of an interpretation, the formula about diophantine constraints
     * and the search for a satisfying interpretation via some solver.
     *
     * @param CpxADPProblem - the original PQDPProblem problem
     * @param allstrict - boolean whether we want to strict all of the rules strictly
     * @param aborter - Aborter to check the timer
     * @return the satisfying polynomial interpretation
     * @throws AbortionException
     */
    private POLO findOrdering(final ADP_Cpx_Problem CpxADPProblem, final boolean allstrict, final Abortion aborter)
        throws AbortionException {

        final Set<FunctionSymbol> constructorSig = getSignatureWithDeAnnoSymbols(CpxADPProblem);
        final Set<FunctionSymbol> definedSig = CpxADPProblem.getDefSignature();
        constructorSig.removeAll(definedSig);

        final POLOSolver solver = this.order.getCPIMLPOLOSolver(definedSig, constructorSig, aborter);
        solver.setAllowWeakMonotonicity(true);

        final Formula<Diophantine> fml = createFormula(CpxADPProblem, solver.getInterpretation(), aborter);

        return solver.solveDioFormula(fml, aborter);
    }

    /**
     * Create the formula that we need to satisfy
     *  1. All expected values are non increasing,
     *  2. The expected value of the terms with annotation (sum) of the rhs needs to strictly decrease
     *
     * @param CpxADPProblem - the original PQDPProblem problem
     * @param interpretation - the polynomial interpretation with variables as coefficients
     * @param aborter - Aborter to check the timer
     * @return The complete formula for the probabilistic RPP
     */
    private Formula<Diophantine> createFormula(final ADP_Cpx_Problem CpxADPProblem,
        final Interpretation interpretation,
        final Abortion aborter) {

        final FormulaFactory<Diophantine> ff = NonCountingCircuitFactory.create(SplitMode.FLATTEN, SplitMode.LEFT_COMB); //TODO: Check these parameters

        final Set<ProbabilisticRule> withAnnoP = CpxADPProblem.getPwithOnlyAnno();
        final Set<ProbabilisticRule> withAnnoS = CpxADPProblem.getSwithOnlyAnno();
        final Set<ProbabilisticRule> probRules = CpxADPProblem.getSWithQ();

        // Create the Formula of Constraints that we want to solve:
        // 1. The expected value is non-increasing for every dependency tuple and every rewrite rule
        final List<Formula<Diophantine>> expectedValueConstraintList = new ArrayList<>();
        for (final ProbabilisticRule probRule : probRules) {
            expectedValueConstraintList.add(createRuleFormulaExpectation(ff, probRule, interpretation, aborter));
        }
        for (final ProbabilisticRule depTuple : withAnnoP) {
            expectedValueConstraintList.add(createDepTupleFormulaExpectation(ff, depTuple, interpretation, CpxADPProblem, aborter));
        }
        final Formula<Diophantine> expectedValueConstraintFormula = ff.buildAnd(expectedValueConstraintList);

        // 2. The expected value of the terms with annotation (sum) of the rhs needs to strictly decrease
        final List<Formula<Diophantine>> removalConstraintList = new ArrayList<>();
        for (final ProbabilisticRule depTuple : withAnnoS) {
            removalConstraintList.add(createDepTupleStrictFormulaExpectation(ff, depTuple, interpretation, CpxADPProblem, aborter));
        }

        Formula<Diophantine> removalConstraintFormula;
        if (this.allstrict) {
            removalConstraintFormula = ff.buildAnd(removalConstraintList);
        } else {
            removalConstraintFormula = ff.buildOr(removalConstraintList);
        }

        // 3. Require CPIs
        final Formula<Diophantine> cpiFormula = createCPIConstraintsFormula(ff, CpxADPProblem, interpretation, aborter);

        final List<Formula<Diophantine>> finalConstraintsList = new ArrayList<>();
        finalConstraintsList.add(expectedValueConstraintFormula);
        finalConstraintsList.add(removalConstraintFormula);
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
        final ADP_Cpx_Problem CpxADPProblem,
        final Interpretation interpretation,
        final Abortion aborter) {

        final Set<FunctionSymbol> constructorSig = getSignatureWithDeAnnoSymbols(CpxADPProblem);
        final Set<FunctionSymbol> definedSig = CpxADPProblem.getDefSignature();
        constructorSig.removeAll(definedSig);

        final List<Formula<Diophantine>> resultFormulaList = new ArrayList<>();

        if (!this.exponential) {
            for (final FunctionSymbol f : constructorSig) {
                for (int i = 0; i < f.getArity(); i++) {
                    final Formula<Diophantine> helpFormula = ff.buildTheoryAtom(interpretation.getCPIConstraintForLinearInterpretation(f, i));
                    resultFormulaList.add(helpFormula);
                }
            }
        }

        if (this.constant) {
            for (final FunctionSymbol f : getSignatureWithDeAnnoSymbols(CpxADPProblem)) {
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
        final ADP_Cpx_Problem CpxADPProblem,
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

            for (final Pair<TRSFunctionApplication, Position> annoSubterm : term.getAnnoSubtermsWithPositions(CpxADPProblem.getDeAnnoMap())) {
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
        final ADP_Cpx_Problem CpxADPProblem,
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

            for (final Pair<TRSFunctionApplication, Position> annoSubterm : term.getAnnoSubtermsWithPositions(CpxADPProblem.getDeAnnoMap())) {
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
    private boolean checkStrictDecrease(final ProbabilisticRule rule, final ADP_Cpx_Problem CpxADPProblem, final POLO order, final Abortion aborter) {
        VarPolynomial lhsTuplePoly = (order.getInterpretation().interpretTerm(rule.getLeft(), aborter));
        VarPolynomial rhsExpectedPoly = VarPolynomial.ZERO;
        //Compute a multiplier such that we are dealing with simple polys at the end with natural coefficients
        BigInteger multiplier = BigInteger.ONE;
        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
            final BigFraction prob = entry.getKey().getValue();
            multiplier = multiplier.multiply(prob.getDenominator());
        }

        // l -> {p1 : r1, ..., pk : rk} add up for each ri the annotated subterms (term = ri)
        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
            final TRSTerm term = entry.getKey().getKey();
            final BigFraction prob = entry.getKey().getValue();
            final Integer amount = entry.getValue();
            // Adding all annotated subterms interpretations to setPoly
            VarPolynomial setPoly = VarPolynomial.ZERO;
            for (final Pair<TRSFunctionApplication, Position> annoSubterm : term.getAnnoSubtermsWithPositions(CpxADPProblem.getDeAnnoMap())) {
                setPoly = setPoly.plus(order.getInterpretation().interpretTerm(annoSubterm.x, aborter));
            }

            final BigInteger multipliesProb = prob.multiply(multiplier).reduce().getNumerator();

            // Adding setpoly, multiplied by the amount, to the rhs expected value
            for (int i = 0; i < amount; i++) {
                rhsExpectedPoly = rhsExpectedPoly.plus(setPoly.times(SimplePolynomial.create(multipliesProb)));
            }
        }

        // We need to multiply the lhs by the total amount we have on the rhs side to compare with the expected value
        lhsTuplePoly = lhsTuplePoly.times(SimplePolynomial.create(multiplier));

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

    public static class CpxADP_ReductionPairProof extends Proof.DefaultProof {

        private final ComplexityValue resultingComplexity;
        private final ExportableOrder<TRSTerm> order;
        private final Set<ProbabilisticRule> orientedPRules;
        private final Set<ProbabilisticRule> keptPRules;

        CpxADP_ReductionPairProof(final ComplexityValue resultingComplexity,
            final ExportableOrder<TRSTerm> order,
            final ADP_Cpx_Problem origqdp,
            final ADP_Cpx_Problem resultingQDP,
            final Set<ProbabilisticRule> orientedPRules,
            final Set<ProbabilisticRule> keptPRules) {
            this.resultingComplexity = resultingComplexity;
            this.order = order;
            this.orientedPRules = orientedPRules;
            this.keptPRules = keptPRules;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            result.append(o.paragraph());
            result.append("We use the reduction pair processor " + o.cite(Citation.KASSING_DISS) + ".");
            result.append(o.linebreak());
            result.append("The following pairs can be oriented strictly and are moved from S:");
            result.append(o.cond_linebreak());
            result.append(o.set(this.orientedPRules, Export_Util.RULES));
            result.append(o.cond_linebreak());
            result.append("The remaining pairs can at least be oriented weakly:");
            result.append(o.cond_linebreak());
            result.append(o.set(this.keptPRules, Export_Util.RULES));
            result.append(o.cond_linebreak());
            result.append("Used ordering:");
            result.append(this.order.export(o));
            result.append(o.cond_linebreak());
            result.append("The complexity of the removed ADPs is bounded by:" + this.resultingComplexity.export(o));
            return result.toString();
        }
    }

    // ================================================================================
    // Arguments Class
    // ================================================================================

    public static class Arguments {

        public boolean allstrict = false;
        public boolean constant = false;
        public boolean exponential = false;
        public SolverFactory order;
    }

}
