package aprove.verification.probabilistic.Termination.ADPProblem.AST.Processors;

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
import aprove.verification.oldframework.BasicStructures.FunctionSymbol;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.ADPProblem.AST.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import immutables.*;

/**
 * Reduction Pair Processor as described in Kassing's master's thesis, CADE23 and FLOPS24 for ADPs
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class ADP_AST_ReductionPairProcessor extends ADP_AST_ProblemProcessor {

    // ================================================================================
    // Properties
    // ================================================================================

    private final boolean allstrict;
    private final SolverFactory order;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    @ParamsViaArgumentObject
    public ADP_AST_ReductionPairProcessor(final Arguments arguments) {
        this.allstrict = arguments.allstrict;
        this.order = arguments.order;
    }

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isAST_ADPApplicable(final ADP_AST_Problem qdp) {
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result processAST_ADPProblem(final ADP_AST_Problem oriqAst_ADP, final Abortion aborter) throws AbortionException {

        final POLO order = findOrdering(oriqAst_ADP, this.allstrict, aborter);

        if (order == null) {
            return ResultFactory.unsuccessful("Could not find a suitable poly interpretation");
        }

        /* find strict tuples */
        final Set<ProbabilisticRule> oldDepTuples = oriqAst_ADP.getP();
        final Set<ProbabilisticRule> keptDepTuples = new HashSet<>();
        final Set<ProbabilisticRule> removedDepTuples = new HashSet<>();
        final ImmutableSet<ProbabilisticRule> oldRules = ImmutableCreator.create(oriqAst_ADP.getS());

        for (final ProbabilisticRule depTuple : oldDepTuples) {
            if (!checkStrictDecrease(depTuple, oriqAst_ADP, order, aborter)) {
                keptDepTuples.add(depTuple);
            } else {
                removedDepTuples.add(depTuple);
            }
        }

        final PQTRSProblem newpqtrs =
            PQTRSProblem.create(oldRules, oriqAst_ADP.getQ(), oriqAst_ADP.getStrat(), ProbabilisticTerminationResult.AST, oriqAst_ADP.isBasic());
        ADP_AST_Problem newpqdp;
        if (oriqAst_ADP.isBasic()) {
            newpqdp = ADP_AST_Problem
                .createBasic(keptDepTuples, oriqAst_ADP.getReach(), newpqtrs, oriqAst_ADP.getReachPQTRS(), oriqAst_ADP.getStrat(), oriqAst_ADP.getBiAnnoMap());
        } else {
            newpqdp = ADP_AST_Problem.create(keptDepTuples, newpqtrs, oriqAst_ADP.getStrat(), oriqAst_ADP.getBiAnnoMap());
        }

        final AST_ADPReductionPairProof RPPproof = new AST_ADPReductionPairProof(order,
            oriqAst_ADP,
            newpqdp,
            removedDepTuples,
            keptDepTuples);

        return ResultFactory.proved(newpqdp, YNMImplication.EQUIVALENT, RPPproof);
    }

    /**
     * The constraints also interpret the de-annotated versions of the annotated symbols. Such a symbol does not
     * occur in the problem anymore if all of its rules and all of its unannotated occurrences have been removed.
     */
    private static Set<FunctionSymbol> getSignatureWithDeAnnoSymbols(final ADP_AST_Problem ast_ADPProblem) {
        final Set<FunctionSymbol> signature = new LinkedHashSet<>(ast_ADPProblem.getSignature());
        for (final FunctionSymbol f : ast_ADPProblem.getSignature()) {
            final FunctionSymbol deAnno = ast_ADPProblem.getDeAnnoMap().get(f);
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
     * @param ast_ADPProblem - the original PQDPProblem problem
     * @param allstrict - boolean whether we want to strict all of the rules strictly
     * @param aborter - Aborter to check the timer
     * @return the satisfying polynomial interpretation
     * @throws AbortionException
     */
    private POLO findOrdering(final ADP_AST_Problem ast_ADPProblem, final boolean allstrict, final Abortion aborter)
        throws AbortionException {

        final POLOSolver solver = this.order.getMLPOLOSolver(getSignatureWithDeAnnoSymbols(ast_ADPProblem), aborter);
        solver.setAllowWeakMonotonicity(true);

        final Formula<Diophantine> fml = createFormula(ast_ADPProblem, solver.getInterpretation(), aborter);

        return solver.solveDioFormula(fml, aborter);
    }

    /**
     * Create the formula that we need to satisfy
     * (All expected values are non increasing, at least one element in the support of the rhs is strictly decreasing)
     *
     * @param ast_ADPProblem - the original PQDPProblem problem
     * @param interpretation - the polynomial interpretation with variables as coefficients
     * @param aborter - Aborter to check the timer
     * @return The complete formula for the probabilistic RPP
     */
    private Formula<Diophantine> createFormula(final ADP_AST_Problem ast_ADPProblem,
        final Interpretation interpretation,
        final Abortion aborter) {

        final FormulaFactory<Diophantine> ff = NonCountingCircuitFactory.create(SplitMode.FLATTEN, SplitMode.LEFT_COMB); //TODO: Check these parameters

        final Set<ProbabilisticRule> depTuples = ast_ADPProblem.getP();
        final Set<ProbabilisticRule> probRules = ast_ADPProblem.getS();

        //Create the Formula of Constraints that we want to solve:
        //1. The expected value is non-increasing for every dependency tuple and every rewrite rule
        final List<Formula<Diophantine>> expectedValueConstraintList = new ArrayList<>();
        for (final ProbabilisticRule probRule : probRules) {
            expectedValueConstraintList.add(createRuleFormulaExpectation(ff, probRule, interpretation, aborter));
        }
        for (final ProbabilisticRule depTuple : depTuples) {
            expectedValueConstraintList.add(createDepTupleFormulaExpectation(ff, depTuple, interpretation, ast_ADPProblem, aborter));
        }
        final Formula<Diophantine> expectedValueConstraintFormula = ff.buildAnd(expectedValueConstraintList);

        //2. Some term needs to be strictly decreasing from the support of the rhs in order to remove it
        final List<Formula<Diophantine>> removalConstraintList = new ArrayList<>();
        for (final ProbabilisticRule depTuple : depTuples) {
            removalConstraintList.add(createDepTupleFormulaSingle(ff, depTuple, ast_ADPProblem, interpretation, aborter));
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
        final ADP_AST_Problem ast_ADPProblem,
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

            for (final Pair<TRSFunctionApplication, Position> annoSubterm : term.getAnnoSubtermsWithPositions(ast_ADPProblem.getDeAnnoMap())) {
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
     * @param rule - the probabilistic rewrite rule for this formula
     * @param interpretation - the polynomial interpretation with variables as coefficients
     * @param aborter - Aborter to check the timer
     * @return formula to encode "one element in the support of rhs is strictly decreasing"
     */
    private Formula<Diophantine> createDepTupleFormulaSingle(final FormulaFactory<Diophantine> ff,
        final ProbabilisticRule rule,
        final ADP_AST_Problem ast_ADPProblem,
        final Interpretation interpretation,
        final Abortion aborter) {
        final VarPolynomial lhsTuplePoly = (interpretation.interpretTerm(rule.getLeft(), aborter));

        final List<Formula<Diophantine>> allFormulasList = new ArrayList<>();

        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
            final List<Formula<Diophantine>> singleRuleFormulaList = new ArrayList<>();

            final TRSTerm term = entry.getKey().getKey();

            final List<Formula<Diophantine>> singleSmallerFormulaList = new ArrayList<>();

            //Make sure that that the Tuple part is strictly smaller
            VarPolynomial setPoly = VarPolynomial.ZERO;
            for (final Pair<TRSFunctionApplication, Position> annoSubterm : term.getAnnoSubtermsWithPositions(ast_ADPProblem.getDeAnnoMap())) {
                setPoly = setPoly.plus(interpretation.interpretTerm(annoSubterm.x, aborter));
            }
            final VarPolynomial tupleConstraint = lhsTuplePoly.minus(setPoly);

            final Pair<Set<SimplePolyConstraint>, SimplePolyConstraint> setSmallerSPCs = new VarPolyConstraint(
                tupleConstraint,
                ConstraintType.GE).createSearchStrictCoefficientConstraints();

            for (final SimplePolyConstraint spc : setSmallerSPCs.x) {
                final Formula<Diophantine> helpFormula = ff.buildTheoryAtom(Diophantine.create(spc));
                singleSmallerFormulaList.add(helpFormula);
            }
            singleSmallerFormulaList.add(ff.buildTheoryAtom(Diophantine.create(setSmallerSPCs.y.getPolynomial(), ConstraintType.GT)));
            final Formula<Diophantine> singleSmaller = ff.buildAnd(singleSmallerFormulaList);
            singleRuleFormulaList.add(singleSmaller);

            //Make sure that that the TRS part is smaller or equal if it is contained in R
            if (ast_ADPProblem.getS().contains(rule.removeAnnos(ast_ADPProblem.getDeAnnoMap()))) {
                final VarPolynomial lhsTermPoly =
                    (interpretation.interpretTerm(rule.getLeft().renameAtAllMap(rule.getLeft().getPositions(), ast_ADPProblem.getDeAnnoMap()), aborter));
                final VarPolynomial termPoly = interpretation.interpretTerm(term.renameAtAllMap(term.getPositions(), ast_ADPProblem.getDeAnnoMap()), aborter);
                final VarPolynomial termConstraint = lhsTermPoly.minus(termPoly);

                final Set<SimplePolyConstraint> termSPCs = new VarPolyConstraint(termConstraint, ConstraintType.GE)
                    .createCoefficientConstraints();

                final List<Formula<Diophantine>> termSmallerOrEqualFormulaList = new ArrayList<>();
                for (final SimplePolyConstraint spc : termSPCs) {
                    final Formula<Diophantine> helpFormula = ff.buildTheoryAtom(Diophantine.create(spc));
                    termSmallerOrEqualFormulaList.add(helpFormula);
                }
                final Formula<Diophantine> termSmallerOrEqualFormula = ff.buildAnd(termSmallerOrEqualFormulaList);
                singleRuleFormulaList.add(termSmallerOrEqualFormula);
            }

            final Formula<Diophantine> singleRHSFormula = ff.buildAnd(singleRuleFormulaList);
            allFormulasList.add(singleRHSFormula);
        }
        return ff.buildOr(allFormulasList);
    }

    /**
     * @param rule - the probabilistic rewrite rule for this formula
     * @param order - the polynomial interpretation that solved the RPP formula
     * @param aborter - Aborter to check the timer
     * @return true, if the rule together with the polynomial interpretation stored in order satisfies the "strictly decreasing" formula
     */
    private boolean checkStrictDecrease(final ProbabilisticRule rule, final ADP_AST_Problem ast_ADPProblem, final POLO order, final Abortion aborter) {
        final VarPolynomial lhsTuplePoly = (order.getInterpretation().interpretTerm(rule.getLeft(), aborter));

        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
            final TRSTerm term = entry.getKey().getKey();
            boolean firstProperty = false;

            //Make sure that that the Tuple part is strictly smaller
            VarPolynomial setPoly = VarPolynomial.ZERO;
            for (final Pair<TRSFunctionApplication, Position> annoSubterm : term.getAnnoSubtermsWithPositions(ast_ADPProblem.getDeAnnoMap())) {
                setPoly = setPoly.plus(order.getInterpretation().interpretTerm(annoSubterm.x, aborter));
            }
            final VarPolynomial tupleConstraintPoly = lhsTuplePoly.minus(setPoly);

            final VarPolyConstraint tupleConstraint = new VarPolyConstraint(tupleConstraintPoly, ConstraintType.GT);
            firstProperty = tupleConstraint.isValid();

            //Make sure that that the TRS part is smaller or equal if it is contained in R
            if (ast_ADPProblem.getS().contains(rule.removeAnnos(ast_ADPProblem.getDeAnnoMap()))) {
                boolean secondProperty = false;

                final VarPolynomial lhsTermPoly = (order.getInterpretation()
                    .interpretTerm(rule.getLeft().renameAtAllMap(rule.getLeft().getPositions(), ast_ADPProblem.getDeAnnoMap()), aborter));
                final VarPolynomial termPoly =
                    order.getInterpretation().interpretTerm(term.renameAtAllMap(term.getPositions(), ast_ADPProblem.getDeAnnoMap()), aborter);
                final VarPolynomial termConstraintPoly = lhsTermPoly.minus(termPoly);

                final VarPolyConstraint termConstraint = new VarPolyConstraint(termConstraintPoly, ConstraintType.GE);
                secondProperty = termConstraint.isValid();

                if (firstProperty && secondProperty) {
                    return true;
                }
            } else {
                if (firstProperty) {
                    return true;
                }
            }
        }
        return false;
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class AST_ADPReductionPairProof extends Proof.DefaultProof {

        private final ExportableOrder<TRSTerm> order;
        private final ADP_AST_Problem origPQDP;
        private final Set<ProbabilisticRule> orientedPRules;
        private final Set<ProbabilisticRule> keptPRules;

        AST_ADPReductionPairProof(final ExportableOrder<TRSTerm> order,
            final ADP_AST_Problem origqdp,
            final ADP_AST_Problem resultingQDP,
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
            if (!this.origPQDP.isBasic()) { //innermost and full AST
                result.append("We use the reduction pair processor " + o.cite(Citation.KASSING_DISS) + ".");
            } else { //basic AST
                result.append("We use the reduction pair processor " + o.cite(Citation.JPK60) + ".");
            }
            result.append(o.linebreak());
            result.append("The following pairs can be oriented strictly and we delete all annotations:");
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
