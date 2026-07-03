package aprove.verification.confluence;

import java.util.*;
import java.util.concurrent.atomic.AtomicInteger;
import java.util.stream.*;

import aprove.prooftree.Obligations.BasicObligation;
import aprove.prooftree.Obligations.BasicObligationNode;
import aprove.solver.SolverFactory;
import aprove.strategies.Abortions.Abortion;
import aprove.strategies.Abortions.AbortionException;
import aprove.strategies.Annotations.ParamsViaArgumentObject;
import aprove.strategies.ExecutableStrategies.RuntimeInformation;
import aprove.verification.confluence.Utility.CPK;
import aprove.verification.confluence.Utility.CriticalPairInfo;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Processor;
import aprove.verification.dpframework.Result;
import aprove.verification.dpframework.ResultFactory;
import aprove.verification.dpframework.TRSProblem.QTRSProblem;
import aprove.verification.oldframework.Algebra.Polynomials.ConstraintType;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolynomial;
import aprove.verification.oldframework.BasicStructures.FunctionSymbol;
import aprove.verification.oldframework.Logic.YNMImplication;
import aprove.verification.oldframework.PropositionalLogic.Formula;
import aprove.verification.oldframework.PropositionalLogic.FormulaFactory;
import aprove.verification.oldframework.PropositionalLogic.Formulae.NonCountingCircuitFactory;
import aprove.verification.oldframework.PropositionalLogic.Formulae.SplitMode;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.Diophantine;
import aprove.verification.oldframework.Utility.GenericStructures.Pair;
import immutables.ImmutableCreator;
import immutables.ImmutableList;


public class QuasiLinearLinearizedDecreasingProcessor implements Processor {
    private final Arguments arguments;

    @ParamsViaArgumentObject
    public QuasiLinearLinearizedDecreasingProcessor(Arguments arguments) {
        this.arguments = arguments;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        ConfTRSProblem confTRSProblem = (ConfTRSProblem) obl;

        // First prove local confluence
        var criticalPairs = confTRSProblem.getCriticalPairs();
        var status = criticalPairs.checkStatusWeak(arguments.WeakCRJoinLimit, aborter);

        // Or fail with unsuccessful. Don't fail with an actual result, because, when using redundant rules, this is only sound, not complete.
        // Therefore, the proof tree would terminate with MAYBE instead of continuing
        if (status != CPK.WCR && status != CPK.WCR_DONE)
            return ResultFactory.unsuccessful();

        QuasiLinearDecreasingProcessorState state = new QuasiLinearDecreasingProcessorState(confTRSProblem, aborter);
        Formula<Diophantine> constraints = state.buildConstraints(criticalPairs.getFoundJoinable());

        var solver = arguments.Order.getPOLOSolver(confTRSProblem.getDefinedSymbolsOfR(), aborter);
        var solution = solver.solveDioFormula(constraints, aborter);
        if (solution == null)
            return ResultFactory.unsuccessful();

        Set<Rule> nonLinearRules = state.getNonLinearRules();
        QTRSProblem innermostTerminationProblem = QTRSProblem.create(ImmutableCreator.create(nonLinearRules)).createInnermost();
        var proof = new QuasiLinearLinearizedDecreasingProof(state.getFunctionSymbolSortAssignment(), nonLinearRules);
        return ResultFactory.provedAnd(List.of(innermostTerminationProblem), YNMImplication.SOUND, proof);
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof ConfTRSProblem;
    }

    public static class Arguments {
        public SolverFactory Order;
        public int WeakCRJoinLimit = 6;
    }

    record NestedSort(int functionSymbolSort, List<Integer> argumentSorts) {
        @Override
        public String toString() {
            return argumentSorts.stream().map(String::valueOf).collect(Collectors.joining("*", "", "->" + functionSymbolSort));
        }
    }

    private record Label(SimplePolynomial ruleWeight) { }

    private static final class QuasiLinearDecreasingProcessorState {
        private final Abortion aborter;
        private final List<Rule> rules;
        private final Map<FunctionSymbol, NestedSort> functionSymbolSortAssignment;
        private final Set<Rule> nonLinearRules;
        private final Map<Rule, Label> ruleLabels;
        private final Map<Label, Set<Label>> ruleLabelClosure;
        private final FormulaFactory<Diophantine> ff = NonCountingCircuitFactory.create(SplitMode.FLATTEN, SplitMode.LEFT_COMB);

        QuasiLinearDecreasingProcessorState(ConfTRSProblem confTRSProblem, Abortion aborter) {
            this.aborter = aborter;
            this.rules = new ArrayList<>(confTRSProblem.getRules());
            ruleLabels = confTRSProblem.getRules().stream().collect(Collectors.toMap(r -> r, r -> new Label(SimplePolynomial.create("w" + rules.indexOf(r)))));
            // Rename the variables of all rules so that V(r) is pairwise disjunct for all rules r
            var renamedRules = renameRules(confTRSProblem.getRules());
            var nonLinearVariablesForRule = computeNonLinearVariablesForRule(renamedRules.getValue());
            nonLinearRules = nonLinearVariablesForRule.entrySet().stream().filter(entry -> entry.getValue().size() > 1).map(Map.Entry::getKey).collect(Collectors.toSet());
            var sortAssignment = computeMaximallyDistinctSortAssignment(renamedRules.getKey(), renamedRules.getValue());
            var variableSortAssignment = sortAssignment.getKey();
            functionSymbolSortAssignment = sortAssignment.getValue();
            ruleLabelClosure = new LinkedHashMap<>();
            for (var entry : nonLinearVariablesForRule.entrySet()) {
                var closure = new LinkedHashSet<Label>();
                var nonLinearVariableSorts = entry.getValue().stream().map(variableSortAssignment::get).collect(Collectors.toSet());
                var subtermClosure = computeSubtermSortRelationClosure(nonLinearVariableSorts, functionSymbolSortAssignment);
                for (Rule rule : rules) {
                    var lhsSort = functionSymbolSortAssignment.get(rule.getRootSymbol()).functionSymbolSort();
                    if (subtermClosure.contains(lhsSort))
                        closure.add(ruleLabels.get(rule));
                }

                ruleLabelClosure.put(ruleLabels.get(entry.getKey()), closure);
            }
        }

        public Set<Rule> getNonLinearRules() {
            return nonLinearRules;
        }

        public Map<FunctionSymbol, NestedSort> getFunctionSymbolSortAssignment() {
            return functionSymbolSortAssignment;
        }

        private static Pair<Set<TRSVariable>, Set<Rule>> renameRules(Set<Rule> rules) {
            Set<TRSVariable> renamedVars = new LinkedHashSet<>();
            Set<Rule> renamedRules = new LinkedHashSet<>();
            for (Rule rule : rules) {
                var renamedRule = rule.renameVariables(renamedVars);
                var renamedVarsInRule = renamedRule.getVariables();
                renamedRules.add(renamedRule);
                renamedVars.addAll(renamedVarsInRule);
            }

            return new Pair<>(renamedVars, renamedRules);
        }

        private Pair<Map<TRSVariable, Integer>, Map<FunctionSymbol, NestedSort>> computeMaximallyDistinctSortAssignment(Set<TRSVariable> renamedVariables, Set<Rule> renamedRules) {
            var functionSymbols = renamedRules.stream().flatMap(rule -> rule.getFunctionSymbols().stream()).collect(Collectors.toSet());

            AtomicInteger i = new AtomicInteger(0);

            // Initially, every symbol is assigned a distinct sort
            var functionSymbolSortAssignment = functionSymbols.stream()
                .collect(
                    Collectors.toMap(
                        f -> f,
                        f -> new NestedSort(
                            i.incrementAndGet(),
                            IntStream.range(i.incrementAndGet(), i.addAndGet(f.getArity()))
                                .boxed()
                                .collect(Collectors.toList())))
                );

            var variableSortAssignment = renamedVariables.stream()
                .collect(Collectors.toMap(
                    v -> v,
                    _ -> i.incrementAndGet())
                );

            // Now, we make the functionSymbolSort assignment consistent, i.e., tau(l) = tau(r) for all rules.
            // This is done by recursively replacing the sort symbol by symbol, and replacing old sort occurrences by new ones
            for (Rule rule : renamedRules) {
                var lhs = rule.getLeft();
                var rhs = rule.getRight();
                var rootSymbolSort = functionSymbolSortAssignment.get(lhs.getRootSymbol()).functionSymbolSort();
                recursivelyFixSortAssignment(lhs, rootSymbolSort, variableSortAssignment, functionSymbolSortAssignment);
                recursivelyFixSortAssignment(rhs, rootSymbolSort, variableSortAssignment, functionSymbolSortAssignment);
            }

            return new Pair<>(variableSortAssignment, functionSymbolSortAssignment);
        }

        // Recursively replaces any occurrences of the sort of `term` with `sort`.
        // The initial sort of a function symbol is always pushed to the argument symbols. For this, every occurrence of the old sort is replaced by the new one.
        private void recursivelyFixSortAssignment(TRSTerm term, int sort, Map<TRSVariable, Integer> variableSortAssignment, Map<FunctionSymbol, NestedSort> functionSymbolSortAssignment) {
            int termSort;
            if (term instanceof TRSFunctionApplication f) {
                var fSort = functionSymbolSortAssignment.get(f.getRootSymbol());
                termSort = fSort.functionSymbolSort();
            } else {
                var v = (TRSVariable) term;
                termSort = variableSortAssignment.get(v);
            }

            variableSortAssignment.replaceAll((_, s) -> s == termSort ? sort : s);
            functionSymbolSortAssignment.replaceAll((_, s) -> {
                var argumentSorts = s.argumentSorts();
                argumentSorts.replaceAll(arg -> arg == termSort ? sort : arg);
                var functionSymbolSort = s.functionSymbolSort() == termSort ? sort : s.functionSymbolSort();
                return new NestedSort(functionSymbolSort, argumentSorts);
            });

            if (term instanceof TRSFunctionApplication f) {
                var fSort = functionSymbolSortAssignment.get(f.getRootSymbol());
                for (int i = 0; i < f.getArity(); i++) {
                    var arg = f.getArgument(i);
                    var argSort = fSort.argumentSorts().get(i);
                    recursivelyFixSortAssignment(arg, argSort, variableSortAssignment, functionSymbolSortAssignment);
                }
            }
        }

        private static Set<Integer> computeSubtermSortRelationClosure(Set<Integer> sorts, Map<FunctionSymbol, NestedSort> functionSymbolSorts) {
            var closure = new HashSet<>(sorts);
            boolean changed = true;
            while (changed) {
                changed = false;
                for (var sort : functionSymbolSorts.values()) {
                    if (!closure.contains(sort.functionSymbolSort()))
                        continue;
                    if (closure.addAll(sort.argumentSorts()))
                        changed = true;
                }
            }

            return closure;
        }

        private static Map<Rule, Set<TRSVariable>> computeNonLinearVariablesForRule(Set<Rule> rules) {
            return rules.stream().collect(Collectors.toMap(r -> r, QuasiLinearDecreasingProcessorState::computeNonLinearVariablesForRule));
        }

        private static Set<TRSVariable> computeNonLinearVariablesForRule(Rule rule) {
            return Stream.of(rule.getLeft(), rule.getRight())
                    .flatMap(term -> term.getVariableCount()
                            .entrySet()
                            .stream()
                            .filter(entry -> entry.getValue() > 1)
                            .map(Map.Entry::getKey))
                    .collect(Collectors.toSet());
        }

        Formula<Diophantine> buildConstraints(Map<CriticalPairInfo, Pair<ImmutableList<RewriteStep>, ImmutableList<RewriteStep>>> joins) throws AbortionException {
            List<Formula<Diophantine>> constraints = new ArrayList<>();
            for (var join : joins.entrySet()) {
                aborter.checkAbortion();

                var cp = join.getKey();
                if (cp.isTrivial())
                    continue;

                var joinSequences = join.getValue();
                boolean xStartsAtS = joinSequences.x.getFirst().substitutedTerm().equals(cp.s());
                var sSequence = xStartsAtS ? joinSequences.x : joinSequences.y;
                var tSequence = xStartsAtS ? joinSequences.y : joinSequences.x;
                var sLabelSequence = sSequence.stream().skip(1).map(RewriteStep::appliedRule).map(ruleLabels::get).toList();
                var tLabelSequence = tSequence.stream().skip(1).map(RewriteStep::appliedRule).map(ruleLabels::get).toList();

                var alpha = ruleLabels.get(cp.sRule());
                var beta = ruleLabels.get(cp.tRule());
                constraints.add(buildConstraintForCriticalPair(alpha, beta, sLabelSequence, tLabelSequence));
            }

            return ff.buildAnd(constraints);
        }

        private Formula<Diophantine> buildGreaterThan(Label a, Label b) {
            return ff.buildTheoryAtom(Diophantine.create(a.ruleWeight(), b.ruleWeight(), ConstraintType.GT));
        }

        private Formula<Diophantine> buildEquals(Label a, Label b) {
            return ff.buildTheoryAtom(Diophantine.create(a.ruleWeight(), b.ruleWeight(), ConstraintType.EQ));
        }

        // Label alpha is greater than all labels in labelsBelow
        private Formula<Diophantine> buildAllLessThan(Label alpha, Collection<Label> labelsBelow) {
            return ff.buildAnd(labelsBelow.stream().map(l -> buildGreaterThan(alpha, l)).toList());
        }

        // Every label in "labelsBelowEither" is below alpha or below beta
        private Formula<Diophantine> buildAllLessThanEither(Label alpha, Label beta, Collection<Label> labelsBelowEither) {
            return ff.buildAnd(labelsBelowEither.stream().map(l -> ff.buildOr(buildGreaterThan(alpha, l), buildGreaterThan(beta, l))).toList());
        }

        private Set<Label> getNonLinearRuleLabelsClosure(List<Label> labels) {
            return labels.stream()
                    .flatMap(label -> ruleLabelClosure.getOrDefault(label, Set.of()).stream())
                    .collect(Collectors.toSet());
        }

        // R_nl(labelsBelow) < alpha
        private Formula<Diophantine> buildNonLinearAllLessThan(Label alpha, List<Label> labelsBelow) {
            return buildAllLessThan(alpha, getNonLinearRuleLabelsClosure(labelsBelow));
        }

        // R_nl(labelsBelowEither) < alpha ∨ beta
        private Formula<Diophantine> buildNonLinearAllLessThanEither(Label alpha, Label beta, List<Label> labelsBelowEither) {
            return buildAllLessThanEither(alpha, beta, getNonLinearRuleLabelsClosure(labelsBelowEither));
        }

        // The conversion is fully below the two peaks
        private Formula<Diophantine> buildAllBelowPeaks(Label alpha, Label beta, List<Label> labelSequence) {
            return ff.buildAnd(buildAllLessThanEither(alpha, beta, labelSequence), buildNonLinearAllLessThanEither(alpha, beta, labelSequence));
        }

        // The pivot is in the right rewrite sequence.
        private Formula<Diophantine> buildPivotRightSequence(Label alpha, Label beta, int pivotIndex, List<Label> leftRightRewriteSequences) {
            var strictlyBelow = leftRightRewriteSequences.subList(0, pivotIndex);
            var pivot = leftRightRewriteSequences.get(pivotIndex);
            var belowEither = leftRightRewriteSequences.subList(pivotIndex + 1, leftRightRewriteSequences.size());
            var belowEitherWithPivot = new LinkedList<>(belowEither);
            belowEitherWithPivot.add(pivot);
            return ff.buildAnd(
                    List.of(
                            buildAllLessThanEither(alpha, beta, strictlyBelow),
                            buildNonLinearAllLessThanEither(alpha, beta, strictlyBelow),
                            buildEquals(alpha, beta),
                            buildNonLinearAllLessThan(beta, belowEitherWithPivot),
                            buildAllLessThan(beta, belowEither)
                    )
            );
        }

        private Formula<Diophantine> buildAllBelowPeaksOrPivotRightSequence(Label alpha, Label beta, List<Label> leftRightRewriteSequences, int leftSequenceSize) {
            List<Formula<Diophantine>> disjunctions = new ArrayList<>(leftRightRewriteSequences.size() + 1);

            disjunctions.add(buildAllBelowPeaks(alpha, beta, leftRightRewriteSequences));

            // Only move the pivot in the right rewrite sequence
            for (int pivot = leftSequenceSize; pivot < leftRightRewriteSequences.size(); pivot++)
                disjunctions.add(buildPivotRightSequence(alpha, beta, pivot, leftRightRewriteSequences));

            return ff.buildOr(disjunctions);
        }

        // The pivot is in the left rewrite sequence, and there is also a pivot in the right rewrite sequence
        private Formula<Diophantine> buildPivotLeftSequence(Label alpha, Label beta, int pivotIndex, List<Label> leftRightRewriteSequences, int leftSequenceSize) {
            var strictlyBelow = leftRightRewriteSequences.subList(0, pivotIndex);
            var pivot = leftRightRewriteSequences.get(pivotIndex); // It's ensured the pivot is always from the left rewrite sequence
            var belowEither = leftRightRewriteSequences.subList(pivotIndex + 1, leftRightRewriteSequences.size());

            List<Formula<Diophantine>> disjunctions = new ArrayList<>(belowEither.size());
            for (int verticalPivotIndex = leftSequenceSize - pivotIndex; verticalPivotIndex < belowEither.size(); verticalPivotIndex++)
                disjunctions.add(buildPivotRightSequence(alpha, beta, verticalPivotIndex, belowEither));

            var strictlyBelowWithPivot = new LinkedList<>(strictlyBelow);
            strictlyBelowWithPivot.add(pivot);

            return ff.buildAnd(
                    List.of(
                            buildAllLessThan(alpha, belowEither),
                            buildEquals(beta, pivot),
                            buildNonLinearAllLessThan(alpha, strictlyBelowWithPivot),
                            ff.buildOr(disjunctions)
                    )
            );
        }

        private Formula<Diophantine> buildConstraintForCriticalPair(Label alpha, Label beta, List<Label> leftRewriteSequence, List<Label> rightRewriteSequence) {
            var leftRightRewriteSequences = new ArrayList<Label>(leftRewriteSequence.size() + rightRewriteSequence.size());
            leftRightRewriteSequences.addAll(leftRewriteSequence);
            leftRightRewriteSequences.addAll(rightRewriteSequence);

            List<Formula<Diophantine>> disjunctions = new ArrayList<>(leftRewriteSequence.size() + 1);
            disjunctions.add(buildAllBelowPeaksOrPivotRightSequence(alpha, beta, leftRightRewriteSequences, leftRewriteSequence.size()));

            for (int horizontalPivotIndex = 0; horizontalPivotIndex < leftRewriteSequence.size(); horizontalPivotIndex++)
                disjunctions.add(buildPivotLeftSequence(alpha, beta, horizontalPivotIndex, leftRightRewriteSequences, leftRewriteSequence.size()));

            return ff.buildOr(disjunctions);
        }
    }
}
