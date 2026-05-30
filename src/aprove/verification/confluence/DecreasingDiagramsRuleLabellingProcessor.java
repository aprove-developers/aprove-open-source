package aprove.verification.confluence;

import aprove.prooftree.Obligations.BasicObligation;
import aprove.prooftree.Obligations.BasicObligationNode;
import aprove.solver.SolverFactory;
import aprove.strategies.Abortions.Abortion;
import aprove.strategies.Abortions.AbortionException;
import aprove.strategies.Annotations.ParamsViaArgumentObject;
import aprove.strategies.ExecutableStrategies.RuntimeInformation;
import aprove.strategies.ExecutableStrategies.Success;
import aprove.verification.confluence.Utility.CPK;
import aprove.verification.confluence.Utility.CriticalPairInfo;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Processor;
import aprove.verification.dpframework.Result;
import aprove.verification.dpframework.ResultFactory;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.PropositionalLogic.Formula;
import aprove.verification.oldframework.PropositionalLogic.FormulaFactory;
import aprove.verification.oldframework.PropositionalLogic.Formulae.NonCountingCircuitFactory;
import aprove.verification.oldframework.PropositionalLogic.Formulae.SplitMode;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.Diophantine;
import aprove.verification.oldframework.Utility.GenericStructures.BiTreeNode;
import aprove.verification.oldframework.Utility.GenericStructures.Pair;

import java.util.*;

public class DecreasingDiagramsRuleLabellingProcessor implements Processor {
    private final Arguments arguments;

    @ParamsViaArgumentObject
    public DecreasingDiagramsRuleLabellingProcessor(Arguments arguments) {
        this.arguments = arguments;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        ConfTRSProblem confTRSProblem = (ConfTRSProblem) obl;

        // First prove local confluence
        var criticalPairs = confTRSProblem.getCriticalPairs();
        LocalConfluenceProcessor wcrProcessor = new LocalConfluenceProcessor();
        var wcrResult = wcrProcessor.process(confTRSProblem, oblNode, aborter, rti);
        var status = criticalPairs.checkStatusWeak(8, aborter);

        // Or fail with the result
        if (!(wcrResult.getStrategy() instanceof Success) || status != CPK.WCR && status != CPK.WCR_DONE)
            return wcrResult;

        // And then apply the decreasing diagrams technique
        var state = new DecreasingDiagramsRuleLabellingProcessorState(criticalPairs, new ArrayList<>(confTRSProblem.getRules()), aborter);

        var constraints = state.buildConstraints();

        var solver = arguments.Order.getPOLOSolver(confTRSProblem.getDefinedSymbolsOfR(), aborter);
        var resultPolyOrder = solver.solveDioFormula(constraints, aborter);
        return resultPolyOrder == null ? ResultFactory.unsuccessful() : ResultFactory.proved(new DecreasingDiagramProof(constraints));
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        // The technique requires left-linearity
        return obl instanceof ConfTRSProblem confTRSProblem && confTRSProblem.isLeftLinear();
    }

    public static class Arguments {
        public SolverFactory Order;
    }

    private record Label(SimplePolynomial ruleWeight, SimplePolynomial contextWeight, SimplePolynomial ruleWeightPrime) { }

    private static class DecreasingDiagramsRuleLabellingProcessorState {
        private final FormulaFactory<Diophantine> ff = NonCountingCircuitFactory.create(SplitMode.FLATTEN, SplitMode.LEFT_COMB);
        private final Map<Pair<TRSFunctionApplication, Integer>, SimplePolynomial> functionVarCache = new LinkedHashMap<>();
        private final Map<Pair<Integer, Boolean>, SimplePolynomial> ruleVarCache = new LinkedHashMap<>();
        private final CriticalPairs criticalPairs;
        private final List<GeneralizedRule> rules;
        private final Abortion aborter;

        public DecreasingDiagramsRuleLabellingProcessorState(CriticalPairs criticalPairs, List<GeneralizedRule> rules, Abortion aborter) {
            this.criticalPairs = criticalPairs;
            this.rules = rules;
            this.aborter = aborter;
        }

        public Formula<Diophantine> buildConstraints() {
            var LDD2Constraints = buildLDD2Constraints();
            var cndConstraints = buildCNDConstraints();
            return ff.buildAnd(LDD2Constraints, cndConstraints);
        }

        private Formula<Diophantine> buildLDD2Constraints() {
            var allCriticalPairs = criticalPairs.getFoundJoinable();
            if (allCriticalPairs.isEmpty())
                return ff.buildConstant(true);
            List<Formula<Diophantine>> constraints = new LinkedList<>();
            for (var join : allCriticalPairs.entrySet()) {
                aborter.checkAbortion();
                var cpInfo = join.getKey();
                if (cpInfo.isTrivial())
                    continue;
                var context = cpInfoToContext(cpInfo);
                // Do not consider self-overlaps at the root position
                if (cpInfo.isRootOverlap() && context.getValue().x.isEmptyPosition())
                    continue;
                var rewriteSequences = join.getValue();
                // Skip the rewrites s <- d -> t
                var leftLabelSequence = rewriteSequences.x.stream().skip(1).map(this::buildRuleLabel).toList();
                var rightLabelSequence = rewriteSequences.y.stream().skip(1).map(this::buildRuleLabel).toList();
                var leftContextWeight = collectFunctionSymbolWeightsFromHoleToRoot(context);
                var weightPoly = SimplePolynomial.plus(leftContextWeight);
                var firstsRuleWeight = getOrAddRuleWeightVar(new Pair<>(rules.indexOf(cpInfo.sRule()) + 1, false));
                var secondRuleWeight = getOrAddRuleWeightVar(new Pair<>(rules.indexOf(cpInfo.tRule()) + 1, false));
                var firstsRuleWeightPrime = getOrAddRuleWeightVar(new Pair<>(rules.indexOf(cpInfo.sRule()) + 1, true));
                var secondRuleWeightPrime = getOrAddRuleWeightVar(new Pair<>(rules.indexOf(cpInfo.tRule()) + 1, true));
                var phiI = new Label(firstsRuleWeight, weightPoly, firstsRuleWeightPrime);
                var psiJ = new Label(secondRuleWeight, SimplePolynomial.ZERO, secondRuleWeightPrime);
                constraints.add(buildLdd2Constraints(phiI, psiJ, leftLabelSequence));
                constraints.add(buildLdd2Constraints(psiJ, phiI, rightLabelSequence));
            }

            return ff.buildAnd(constraints);
        }

        private static BiTreeNode<Pair<Position, TRSTerm>> cpInfoToContext(CriticalPairInfo cpInfo) {
            var tree = cpInfo.s().getTreeRep();
            return searchForPosition(tree, cpInfo.p());
        }

        private static BiTreeNode<Pair<Position, TRSTerm>> searchForPosition(BiTreeNode<Pair<Position, TRSTerm>> current, Position pos) {
            if (current.getValue().x.equals(pos))
                return current;

            for (var child : current.getChildren()) {
                var found = searchForPosition(child, pos);
                if (found != null)
                    return found;
            }

            return null;
        }

        private Formula<Diophantine> buildLdd2Constraints(Label phi, Label psi, List<Label> rewriteSequence) {
            Formula<Diophantine> allLess = ff.buildAnd(rewriteSequence.stream().map(l -> ff.buildOr(
                            buildLexicographicLessThan(l, phi),
                            buildLexicographicLessThan(l, psi)))
                    .toList());

            int n = rewriteSequence.size();
            List<Formula<Diophantine>> pivotDisjunctions = new ArrayList<>(n);
            List<Formula<Diophantine>> parts = new ArrayList<>(n);

            for (int k = 0; k < n; k++) {
                parts.clear();

                for (int l = 0; l < k; l++)
                    parts.add(buildLexicographicLessThan(rewriteSequence.get(l), phi));

                parts.add(buildLexicographicEquals(rewriteSequence.get(k), psi));

                for (int l = k + 1; l < n; l++)
                    parts.add(ff.buildOr(buildLexicographicLessThan(rewriteSequence.get(l), phi), buildLexicographicLessThan(rewriteSequence.get(l), psi)));

                pivotDisjunctions.add(ff.buildAnd(parts));
            }

            Formula<Diophantine> pivot = ff.buildOr(pivotDisjunctions);
            return ff.buildOr(allLess, pivot);
        }

        private Formula<Diophantine> buildLexicographicLessThan(Label lhs, Label rhs) {
            var firstQuasiOrder = buildLexicographicLessThan(lhs.contextWeight, lhs.ruleWeight, rhs.contextWeight, rhs.ruleWeight);
            var secondQuasiOrder = buildLexicographicLessThan(lhs.ruleWeightPrime, lhs.contextWeight, rhs.ruleWeightPrime, rhs.contextWeight);
            return ff.buildOr(firstQuasiOrder, secondQuasiOrder);
        }

        private Formula<Diophantine> buildLexicographicLessThan(SimplePolynomial phi, SimplePolynomial i, SimplePolynomial rho, SimplePolynomial j) {
            var phiLessRho = ff.buildTheoryAtom(Diophantine.create(rho, phi, ConstraintType.GT));
            var lexEquals = buildLexicographicEquals(phi, i, rho, j);
            return ff.buildOr(phiLessRho, lexEquals);
        }

        private Formula<Diophantine> buildLexicographicEquals(SimplePolynomial phi, SimplePolynomial i, SimplePolynomial rho, SimplePolynomial j) {
            var phiEqualsRho = ff.buildTheoryAtom(Diophantine.create(phi, rho, ConstraintType.EQ));
            var iLessJ = ff.buildTheoryAtom(Diophantine.create(j, i, ConstraintType.GT));
            return ff.buildAnd(phiEqualsRho, iLessJ);
        }

        private Formula<Diophantine> buildLexicographicEquals(Label lhs, Label rhs) {
            var firstQuasiOrder = buildLexicographicEquals(lhs.contextWeight, lhs.ruleWeight, rhs.contextWeight, rhs.ruleWeight);
            var secondQuasiOrder = buildLexicographicEquals(lhs.ruleWeightPrime, lhs.contextWeight, rhs.ruleWeightPrime, rhs.contextWeight);
            return ff.buildOr(firstQuasiOrder, secondQuasiOrder);
        }

        private Label buildRuleLabel(RewriteStep step) {
            // Find the subterm that was replaced by the rule application
            // This subterm is then the hole from which we collect the function symbols outwards and build the weight polynomial
            var tree = step.originalTerm().getTreeRep();
            var context = searchForPosition(tree, step.position());
            var functionWeights = collectFunctionSymbolWeightsFromHoleToRoot(context);
            var contextWeight = SimplePolynomial.plus(functionWeights);
            var ruleWeightVar = getOrAddRuleWeightVar(new Pair<>(rules.indexOf(step.appliedRule()) + 1, false));
            var ruleWeightVarPrime = getOrAddRuleWeightVar(new Pair<>(rules.indexOf(step.appliedRule()) + 1, true));
            return new Label(ruleWeightVar, contextWeight, ruleWeightVarPrime);
        }

        private Formula<Diophantine> buildCNDConstraints() {
            List<Formula<Diophantine>> constraints = new LinkedList<>();
            for (GeneralizedRule rule : rules) {
                aborter.checkAbortion();
                var leftTree = rule.getLeft().getTreeRep();
                var rightTree = rule.getRight().getTreeRep();
                var rightLeaves = rightTree.getLeaves();
                // Iterate over all variables occurring on the lhs
                for (var context : leftTree.getLeaves()) {
                    if (!(context.getValue().y instanceof TRSVariable leftContextVar) || context.getValue().x.isEmptyPosition())
                        continue;
                    var leftWeights = collectFunctionSymbolWeightsFromHoleToRoot(context);
                    if (leftWeights.isEmpty())
                        continue;
                    var matchingRhsVarNodes = rightLeaves.stream().filter(node -> node.getValue().y instanceof TRSVariable rightContextVar && rightContextVar.equals(leftContextVar)).toList();
                    // The rhs of the rule does not contain the context variable
                    if (matchingRhsVarNodes.isEmpty())
                        continue;
                    var constraintLhs = SimplePolynomial.plus(leftWeights);
                    var isRhsLinear = matchingRhsVarNodes.size() == 1;
                    ConstraintType constraintType = isRhsLinear ? ConstraintType.GE : ConstraintType.GT;
                    for (var matchingRhsVarNode : matchingRhsVarNodes) {
                        var rightWeights = collectFunctionSymbolWeightsFromHoleToRoot(matchingRhsVarNode);
                        if (rightWeights.isEmpty())
                            continue;
                        var constraintRhs = SimplePolynomial.plus(rightWeights);
                        if (constraintLhs.equals(constraintRhs))
                            continue;
                        var dio = Diophantine.create(constraintLhs, constraintRhs, constraintType);
                        var dioFormula = ff.buildTheoryAtom(dio);
                        constraints.add(dioFormula);
                    }
                }
            }

            return ff.buildAnd(constraints);
        }

        private SimplePolynomial getOrAddFunctionWeightVar(Pair<TRSFunctionApplication, Integer> functionApplication) {
            return functionVarCache.computeIfAbsent(functionApplication, f -> SimplePolynomial.create("z_" + f.x.getFunctionSymbol().getName() + "." + f.y));
        }

        private SimplePolynomial getOrAddRuleWeightVar(Pair<Integer, Boolean> rule) {
            return ruleVarCache.computeIfAbsent(rule, r -> SimplePolynomial.create("w_" + (rule.y ? "p" : "") + r.x));
        }

        private List<SimplePolynomial> collectFunctionSymbolWeightsFromHoleToRoot(BiTreeNode<Pair<Position, TRSTerm>> hole) {
            List<SimplePolynomial> terms = new LinkedList<>();
            if (hole.isRoot())
                return terms;

            int localHolePosition = hole.getValue().x.lastIndex() + 1;
            BiTreeNode<Pair<Position, TRSTerm>> current = hole.getParent();
            while (current != null) {
                var pair = new Pair<>((TRSFunctionApplication) current.getValue().y, localHolePosition);
                var weightVar = getOrAddFunctionWeightVar(pair);
                terms.add(weightVar);
                if (current.isRoot())
                    break;
                localHolePosition = current.getValue().x.lastIndex() + 1;
                current = current.getParent();
            }

            return terms;
        }
    }
}
