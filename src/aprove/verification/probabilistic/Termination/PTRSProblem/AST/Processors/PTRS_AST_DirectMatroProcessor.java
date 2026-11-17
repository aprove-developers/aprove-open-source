package aprove.verification.probabilistic.Termination.PTRSProblem.AST.Processors;

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
import aprove.verification.oldframework.Algebra.Matrices.*;
import aprove.verification.oldframework.Algebra.Matrices.Interpretation.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import immutables.*;

/**
 * Processor that tries to order the rules of a PTRS
 * directly using polynomial interpretations.
 * Uses the orderings to prove AST.
 *
 * @author J-C Kassing & Jonas Säuberlich
 * @version $Id$
 */
public class PTRS_AST_DirectMatroProcessor extends PTRS_AST_ProblemProcessor {

    // ================================================================================
    // Properties
    // ================================================================================

    private final boolean allstrict;

    private final SolverFactory order;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    @ParamsViaArgumentObject
    public PTRS_AST_DirectMatroProcessor(final Arguments arguments) {
        this.allstrict = arguments.allstrict;
        this.order = arguments.order;
    }

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isPTRSApplicable(final PTRSProblem ptrs) {
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
        Set<Integer> eSet = new HashSet<>();

        while (!toOrderRules.isEmpty()) {
            final Pair<MATRO, Set<Integer>> orderE = findOrdering(ptrs, toOrderRules, this.allstrict, aborter);
            final MATRO order = orderE.getKey();
            eSet = orderE.getValue();

            if (order == null) {
                return ResultFactory.unsuccessful("Could not find a suitable matrix interpretation");
            }

            /* find strict tuples */
            final Set<ProbabilisticRule> removedRules = new HashSet<>();

            for (final ProbabilisticRule rule : toOrderRules) {
                if (checkStrictDecrease(rule, order, eSet, aborter)) {
                    removedRules.add(rule);
                }
            }
            toOrderRules.removeAll(removedRules);

            orderList.add(order);
            removedRulesList.add(removedRules);
        }

        final ASTDirectMatroPTRSProof MATROproof = new ASTDirectMatroPTRSProof(orderList, ptrs, removedRulesList, eSet);

        return ResultFactory.proved(MATROproof);
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
    private Pair<MATRO, Set<Integer>>
        findOrdering(final PTRSProblem ptrs, final Set<ProbabilisticRule> toOrderRules, final boolean allstrict, final Abortion aborter)
            throws AbortionException {

        final MATROSolver solver = this.order.getMLMATROSolver(ImmutableCreator.create(new HashSet<FunctionSymbol>()),
            ptrs.getSignature(),
            ImmutableCreator.create(ptrs.getVariables()),
            aborter);
        final MatrixFactory fact = solver.getFact();
        final int size = fact.createNullMatrix().getNumRows();
        final Set<Integer> upToNumCols = new HashSet<>();
        for (int i = 0; i < size; i++) {
            upToNumCols.add(i);
        }
        final PowerSet<Integer> allECols = new PowerSet<>(upToNumCols);

        for (final Set<Integer> eCols : allECols) {
            if (!eCols.isEmpty()) {
                final MATROSolver oneTimeSolver = this.order.getMLMATROSolver(ImmutableCreator.create(new HashSet<FunctionSymbol>()),
                    ptrs.getSignature(),
                    ImmutableCreator.create(ptrs.getVariables()),
                    aborter);
                final Formula<Diophantine> fml = createFormula(ptrs, toOrderRules, oneTimeSolver.getInterpretation(), eCols, aborter);
                final MATRO sol = oneTimeSolver.solveDioFormula(fml, aborter);
                if (sol != null) {
                    return new Pair<>(sol, eCols);
                }
            }
        }

        return new Pair<>(null, null);
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
        final Set<ProbabilisticRule> toOrderRules,
        final TermInterpretor interpretation,
        final Set<Integer> eCols,
        final Abortion aborter) {

        final FormulaFactory<Diophantine> ff = NonCountingCircuitFactory.create(SplitMode.FLATTEN, SplitMode.LEFT_COMB); //TODO: Check these parameters

        final Set<ProbabilisticRule> probRules = ptrs.getPR();

        //Create the Formula of Constraints that we want to solve:
        //1. The expected value is non-increasing for every dependency tuple and every rewrite rule
        final List<Formula<Diophantine>> expectedValueConstraintList = new ArrayList<>();
        for (final ProbabilisticRule probRule : probRules) {
            expectedValueConstraintList.add(createRuleFormulaExpectation(ff, probRule, interpretation, aborter));
        }
        final Formula<Diophantine> expectedValueConstraintFormula = ff.buildAnd(expectedValueConstraintList);

        //2. Some term needs to be strictly decreasing from the support of the rhs in order to remove it
        //This only focuses on the rules that still need to be ordered.
        final List<Formula<Diophantine>> removalConstraintList = new ArrayList<>();
        for (final ProbabilisticRule rule : toOrderRules) {
            removalConstraintList.add(createFormulaSingleDecrease(ff, rule, interpretation, eCols, aborter));
        }
        Formula<Diophantine> removalConstraintFormula;

        if (this.allstrict) {
            removalConstraintFormula = ff.buildAnd(removalConstraintList);
        } else {
            removalConstraintFormula = ff.buildOr(removalConstraintList);
        }

        final List<Formula<Diophantine>> finalConstraintsList = new ArrayList<>();

        //3. Add monotonicity constraints: Ensure that every Matrix C_i is >=1 at position (0,0)

        final SymbolRepresentations syRes = interpretation.getRepresentations();
        final List<Formula<Diophantine>> monotonicityFormulaList = new ArrayList<>();
        for (final Entry<FunctionSymbol, Map<Integer, Matrix>> e : syRes.getFuncArgSyms().entrySet()) {
            final Map<Integer, Matrix> m = e.getValue();
            if (!m.isEmpty()) {
                for (final Entry<Integer, Matrix> e2 : m.entrySet()) {
                    final Matrix monotonicityMat = e2.getValue();
                    final List<Formula<Diophantine>> andMonoConstraintsList = new ArrayList<>();
                    for (int i = 0; i < monotonicityMat.getNumCols(); i++) {
                        if (eCols.contains(i)) {
                            final Set<SimplePolyConstraint> orMonoConstraints = new LinkedHashSet<>();
                            final List<Formula<Diophantine>> orMonoConstraintsList = new ArrayList<>();
                            for (int j = 0; j < monotonicityMat.getNumRows(); j++) {
                                if (eCols.contains(j)) {
                                    final VarPolynomial p = monotonicityMat.get(j, i).plus(VarPolynomial.create(-1));
                                    orMonoConstraints.addAll(new VarPolyConstraint(p, ConstraintType.GE).createCoefficientConstraints());
                                }
                            }
                            for (final SimplePolyConstraint spc : orMonoConstraints) {
                                final Formula<Diophantine> helpFormula = ff.buildTheoryAtom(Diophantine.create(spc));
                                orMonoConstraintsList.add(helpFormula);
                            }
                            andMonoConstraintsList.add(ff.buildOr(orMonoConstraintsList));
                        }

                    }
                    if (!andMonoConstraintsList.isEmpty()) {
                        monotonicityFormulaList.add(ff.buildAnd(andMonoConstraintsList));
                    }

                }
            }
        }

        final Formula<Diophantine> monotonicityFormula = ff.buildAnd(monotonicityFormulaList);

        finalConstraintsList.add(expectedValueConstraintFormula);
        finalConstraintsList.add(removalConstraintFormula);
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
        final TermInterpretor interpretation,
        final Abortion aborter) {

        Matrix rhsExpectedMatrix = interpretation.getFact().createNullMatrix();

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
                rhsExpectedMatrix = rhsExpectedMatrix.add(
                    interpretation.interpretTerm(term).multiplyScalar(SimplePolynomial.create(multipliesProb)));
            }
        }

        final Matrix lhsMat = (interpretation.interpretTerm(rule.getLeft())).multiplyScalar(SimplePolynomial.create(multiplier));
        final Matrix constraints = lhsMat.minus(rhsExpectedMatrix);
        final Set<SimplePolyConstraint> simplePolyConstraintSet = new LinkedHashSet<>();
        for (final VarPolynomial constraint : constraints.getCompleteList()) {
            simplePolyConstraintSet.addAll(new VarPolyConstraint(constraint, ConstraintType.GE).createCoefficientConstraints());
        }
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
    private Formula<Diophantine> createFormulaSingleDecrease(final FormulaFactory<Diophantine> ff,
        final ProbabilisticRule rule,
        final TermInterpretor interpretation,
        final Set<Integer> eCols,
        final Abortion aborter) {

        final Matrix lhsMat = (interpretation.interpretTerm(rule.getLeft()));

        final List<Formula<Diophantine>> allFormulasList = new ArrayList<>();

        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
            final TRSTerm term = entry.getKey().getKey();

            // ensures that each row is equal to or greater than
            final Matrix singleRhsMat = (interpretation.interpretTerm(term));
            final List<VarPolynomial> constraints = lhsMat.minus(singleRhsMat).getCompleteList();
            final List<Formula<Diophantine>> smallerEqualsFormulaList = new ArrayList<>();
            // make sure every entry is smaller equals
            for (final VarPolynomial singleGreaterConstraint : constraints) {
                final Pair<Set<SimplePolyConstraint>, SimplePolyConstraint> setSmallerSPCs =
                    new VarPolyConstraint(singleGreaterConstraint, ConstraintType.GE).createSearchStrictCoefficientConstraints();
                for (final SimplePolyConstraint spc : setSmallerSPCs.x) {
                    final Formula<Diophantine> helpFormula = ff.buildTheoryAtom(Diophantine.create(spc));
                    smallerEqualsFormulaList.add(helpFormula);
                }
                smallerEqualsFormulaList
                    .add(ff.buildTheoryAtom(Diophantine.create(setSmallerSPCs.y.getPolynomial(), ConstraintType.GE)));
            }
            // ensures that one row that is in E is greater than, only needs to add the constant part
            final List<Formula<Diophantine>> singleSmallerFormulaList = new ArrayList<>();
            for (int i = 0; i < constraints.size(); i++) {
                if (eCols.contains(i)) {
                    final Pair<Set<SimplePolyConstraint>, SimplePolyConstraint> setSmallerSPCs =
                        new VarPolyConstraint(constraints.get(i), ConstraintType.GE).createSearchStrictCoefficientConstraints();
                    singleSmallerFormulaList
                        .add(ff.buildTheoryAtom(Diophantine.create(setSmallerSPCs.y.getPolynomial(), ConstraintType.GT)));
                }
            }
            if (!singleSmallerFormulaList.isEmpty()) {
                allFormulasList.add(ff.buildAnd(ff.buildAnd(smallerEqualsFormulaList), ff.buildOr(singleSmallerFormulaList)));
            }

        }
        return ff.buildOr(allFormulasList);
    }

    /**
     * @param rule - the probabilistic rewrite rule for this formula
     * @param order - the polynomial interpretation that solved the RPP formula
     * @param aborter - Aborter to check the timer
     * @return true, if the rule together with the polynomial interpretation stored in order satisfies the "strictly decreasing" formula
     */
    private boolean checkStrictDecrease(final ProbabilisticRule rule, final MATRO order, final Set<Integer> eCols, final Abortion aborter) {
        final Matrix lhsTermMat = (order.getInterpretation().interpretTerm(rule.getLeft()));

        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
            final TRSTerm term = entry.getKey().getKey();

            //Make sure that that the rhs is strictly smaller
            final Matrix termMat = order.getInterpretation().interpretTerm(term);

            // At least one Entry in E is strictly greater
            boolean oneStrict = false;
            final List<VarPolynomial> diffs = lhsTermMat.minus(termMat).getCompleteList();
            for (int i = 0; i < diffs.size(); i++) {
                if (!eCols.contains(i)) {
                    continue;
                }
                final VarPolyConstraint termConstraint = new VarPolyConstraint(diffs.get(i), ConstraintType.GT);
                if (termConstraint.isValid()) {
                    oneStrict = true;
                    break;
                }
            }
            if (!oneStrict) {
                continue;
            }

            // all entries are greater equal
            boolean allGE = true;
            for (final VarPolynomial termConstraintMat : lhsTermMat.minus(termMat).getCompleteList()) {
                final VarPolyConstraint termConstraint = new VarPolyConstraint(termConstraintMat, ConstraintType.GE);
                if (!termConstraint.isValid()) {
                    allGE = false;
                    break;
                }
            }
            if (allGE) {
                return true;
            }
        }
        return false;
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class ASTDirectMatroPTRSProof extends Proof.DefaultProof {

        private final List<ExportableOrder<TRSTerm>> orderList;
        private final List<Set<ProbabilisticRule>> removedRulesList;
        private final Set<Integer> eSet;

        ASTDirectMatroPTRSProof(final List<ExportableOrder<TRSTerm>> orderList,
            final PTRSProblem origPTRS,
            final List<Set<ProbabilisticRule>> removedRulesList,
            final Set<Integer> eSet) {
            this.orderList = orderList;
            this.removedRulesList = removedRulesList;
            this.eSet = eSet;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            result.append(o.paragraph());
            result.append(
                "We use the direct application of matrix interpretations " + o.cite(Citation.KASSING_DISS) + " with E chosen as " + this.eSet.toString() + ".");

            result.append(o.linebreak());
            for (int i = 0; i < this.orderList.size(); i++) {
                result.append("We can the following rules strictly: ");
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
