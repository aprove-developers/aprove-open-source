package aprove.verification.confluence;

import aprove.prooftree.Obligations.BasicObligation;
import aprove.prooftree.Obligations.BasicObligationNode;
import aprove.solver.Engines.SMTEngine;
import aprove.solver.Engines.SMTLIBEngine;
import aprove.solver.Engines.WrongLogicException;
import aprove.strategies.Abortions.Abortion;
import aprove.strategies.Abortions.AbortionException;
import aprove.strategies.Annotations.ParamsViaArgumentObject;
import aprove.strategies.ExecutableStrategies.RuntimeInformation;
import aprove.verification.dpframework.BasicStructures.Rule;
import aprove.verification.dpframework.BasicStructures.TRSFunctionApplication;
import aprove.verification.dpframework.BasicStructures.TRSTerm;
import aprove.verification.dpframework.BasicStructures.TRSVariable;
import aprove.verification.dpframework.Processor;
import aprove.verification.dpframework.Result;
import aprove.verification.dpframework.ResultFactory;
import aprove.verification.oldframework.BasicStructures.FunctionSymbol;
import aprove.verification.oldframework.Logic.YNM;
import aprove.verification.oldframework.PropositionalLogic.Formula;
import aprove.verification.oldframework.PropositionalLogic.FormulaFactory;
import aprove.verification.oldframework.PropositionalLogic.Formulae.NonCountingCircuitFactory;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.SMTLIBIntEquals;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.SMTLIBIntGE;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.SMTLIBIntGT;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.SMTLIBIntLE;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntConstant;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions.SMTLIBIntMinus;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions.SMTLIBIntMod;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions.SMTLIBIntMult;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions.SMTLIBIntPlus;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntValue;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntVariable;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBTheoryAtom;
import aprove.verification.oldframework.Utility.FreshNameGenerator;
import immutables.ImmutableCreator;
import immutables.ImmutableSet;

import java.math.BigInteger;
import java.util.*;
import java.util.stream.IntStream;

public class PolyomialInterpretationNonConfluenceProcessor implements Processor {
    private final Arguments arguments;
    private final SMTEngine smtEngine = new SMTLIBEngine();

    @ParamsViaArgumentObject
    public PolyomialInterpretationNonConfluenceProcessor(Arguments arguments) {
        this.arguments = arguments;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        var confTrsProblem = (ConfTRSProblem) obl;

        var oneStepUnfolding = computeOneStepUnfolding(confTrsProblem.getRules());
        var newConfTrsProblem = ConfTRSProblem.create(ImmutableCreator.create(oneStepUnfolding));
        var criticalPairs = newConfTrsProblem.getCriticalPairs().getAllFoundCriticalPairs(aborter);
        var state = new PolynomialInterpretationNonConfluenceProcessorState(arguments, aborter, smtEngine);

        int limit = arguments.MaxNumberOfCriticalPairs;
        for (var candidate : criticalPairs) {
            if (limit <= 0)
                break;

            if (candidate.isTrivial() || !(candidate.s().isGroundTerm() && candidate.t().isGroundTerm()))
                continue;

            var result = state.disproveByPolynomialInterpretation(candidate.s(), candidate.t(), confTrsProblem.getRules());

            if (result == null)
                result = state.disproveByOrdering(candidate.s(), candidate.t(), confTrsProblem);

            if (result != null)
                return ResultFactory.disproved(new NotCRProof(candidate.divergence(), candidate.s(), candidate.t()));

            limit--;
        }

        return ResultFactory.unsuccessful();
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof ConfTRSProblem;
    }

    public static class Arguments {
        public int MaxNumberOfCriticalPairs = 100;
        public int Modulus = 3;
    }

    private static Set<Rule> computeOneStepUnfolding(Set<Rule> rules) {
        Set<Rule> result = new HashSet<>(rules);
        for (var rule : rules) {
            result.addAll(forwardUnfold(rule, rules));
            result.addAll(backwardUnfold(rule, rules));
        }

        return result;
    }

    private static Set<Rule> forwardUnfold(Rule rule, Set<Rule> allRules) {
        Set<Rule> res = new HashSet<>();
        TRSTerm lhs = rule.getLeft();
        TRSTerm rhs = rule.getRight();

        for (var subtermWithPosition : rhs.getPositionsWithSubTerms()) {
            for (Rule other : allRules) {
                Rule otherFresh = other.renameVariables(other.getVariables());
                TRSFunctionApplication otherLhs = otherFresh.getLeft();
                TRSTerm otherRhs = otherFresh.getRight();
                var mgu = otherLhs.getMGU(subtermWithPosition.y);
                if (mgu != null) {
                    TRSFunctionApplication newLhs = (TRSFunctionApplication) lhs.applySubstitution(mgu);
                    TRSTerm newRhs = rhs.replaceAt(subtermWithPosition.x, otherRhs).applySubstitution(mgu);
                    res.add(Rule.create(newLhs, newRhs));
                }
            }
        }

        return res;
    }

    private static Set<Rule> backwardUnfold(Rule rule, Set<Rule> allRules) {
        Set<Rule> res = new HashSet<>();
        TRSTerm lhs = rule.getLeft();
        TRSTerm rhs = rule.getRight();

        for (var subtermWithPosition : lhs.getPositionsWithSubTerms()) {
            for (Rule other : allRules) {
                Rule otherFresh = other.renameVariables(other.getVariables());
                TRSFunctionApplication otherLhs = otherFresh.getLeft();
                TRSTerm otherRhs = otherFresh.getRight();
                var mgu = otherRhs.getMGU(subtermWithPosition.y);
                if (mgu != null) {
                    TRSFunctionApplication newLhs = (TRSFunctionApplication) lhs.replaceAt(subtermWithPosition.x, otherLhs).applySubstitution(mgu);
                    TRSTerm newRhs = rhs.applySubstitution(mgu);
                    res.add(Rule.create(newLhs, newRhs));
                }
            }
        }

        return res;
    }

    private static class PolynomialInterpretationNonConfluenceProcessorState {
        private final Arguments arguments;
        private final Abortion aborter;
        private final SMTEngine smtEngine;
        private final FormulaFactory<SMTLIBTheoryAtom> ff = new NonCountingCircuitFactory<>();
        private final Map<FunctionSymbol, List<SMTLIBIntVariable>> functionCoefficients = new LinkedHashMap<>();
        private final Map<TRSVariable, SMTLIBIntVariable> variables = new LinkedHashMap<>();

        private PolynomialInterpretationNonConfluenceProcessorState(Arguments arguments, Abortion aborter, SMTEngine smtEngine) {
            this.arguments = arguments;
            this.aborter = aborter;
            this.smtEngine = smtEngine;
        }

        private Map<String, String> disproveByPolynomialInterpretation(TRSTerm s, TRSTerm t, Set<Rule> rules) {
            var usableRules = computeUsableRules(rules, s);
            usableRules.addAll(computeUsableRules(rules, t));
            List<SMTLIBTheoryAtom> rulesEqualZeroModK = new LinkedList<>();

            var modulus = SMTLIBIntConstant.create(BigInteger.valueOf(arguments.Modulus));
            var zero = SMTLIBIntConstant.create(BigInteger.ZERO);

            var sEncoding = encodeTerm(s);
            var tEncoding = encodeTerm(t);
            var sMinusT = SMTLIBIntMinus.create(List.of(sEncoding, tEncoding));
            var sMinusTModK = SMTLIBIntMod.create(List.of(sMinusT, modulus));
            var sEqualsTModKEqualsZero = SMTLIBIntEquals.create(sMinusTModK, zero);

            for (var rule : usableRules) {
                var lhs = encodeTerm(rule.getLeft());
                var rhs = encodeTerm(rule.getRight());
                var lhsMinusRhs = SMTLIBIntMinus.create(List.of(lhs, rhs));
                var lhsMinusRhsModK = SMTLIBIntMinus.create(List.of(lhsMinusRhs, modulus));
                rulesEqualZeroModK.add(SMTLIBIntEquals.create(lhsMinusRhsModK, zero));
            }

            Formula<SMTLIBTheoryAtom> notSEqualsTModK = ff.buildNot(ff.buildTheoryAtom(sEqualsTModKEqualsZero));
            Formula<SMTLIBTheoryAtom> allRulesEqualZeroModK = ff.buildAnd(ff.buildTheoryAtoms(rulesEqualZeroModK));

            Formula<SMTLIBTheoryAtom> allVarsGEZero = ff.buildAnd(variables.values().stream().map(v -> ff.buildTheoryAtom(SMTLIBIntGE.create(v, zero))).toList());
            Formula<SMTLIBTheoryAtom> allFunctionVarsGEZero = ff.buildAnd(functionCoefficients.values().stream().flatMap(List::stream).map(v -> ff.buildTheoryAtom(SMTLIBIntGE.create(v, zero))).toList());

            try {
                var result = smtEngine.solve(List.of(allVarsGEZero, allFunctionVarsGEZero, notSEqualsTModK, allRulesEqualZeroModK), SMTEngine.SMTLogic.QF_LIA, aborter);
                if (result.x == YNM.YES)
                    return result.y;
                return null;
            } catch (WrongLogicException e) {
                return null;
            }
        }

        private Map<String, String> disproveByOrdering(TRSTerm s, TRSTerm t, ConfTRSProblem confTRSProblem) {
            var rules = confTRSProblem.getRules();
            var usableRulesS = computeUsableRules(rules, s);
            var usableRulesT = computeUsableRules(rules, t);

            List<SMTLIBTheoryAtom> constraints = new LinkedList<>();

            for (var rule : usableRulesS) {
                var lhs = encodeTerm(rule.getLeft());
                var rhs = encodeTerm(rule.getRight());
                var lhsLessEqualsRhs = SMTLIBIntLE.create(lhs, rhs);
                constraints.add(lhsLessEqualsRhs);
            }

            for (var rule : usableRulesT) {
                var lhs = encodeTerm(rule.getLeft());
                var rhs = encodeTerm(rule.getRight());
                var lhsGreaterEqualsRhs = SMTLIBIntGE.create(lhs, rhs);
                constraints.add(lhsGreaterEqualsRhs);
            }

            var sEncoding = encodeTerm(s);
            var tEncoding = encodeTerm(t);
            var sGreaterThanT = SMTLIBIntGT.create(sEncoding, tEncoding);
            constraints.add(sGreaterThanT);

            var conjunction = ff.buildAnd(ff.buildTheoryAtoms(constraints));

            try {
                var result = smtEngine.solve(List.of(conjunction), SMTEngine.SMTLogic.QF_LIA, aborter);
                if (result.x == YNM.YES)
                    return result.y;
                return null;
            } catch (WrongLogicException e) {
                return null;
            }
        }

        /*private Map<String, String> disproveByRecursivePathOrdering(TRSTerm s, TRSTerm t, Set<Rule> rules) {

        }*/

        private SMTLIBIntValue encodeTerm(TRSTerm term) {
            if (term instanceof TRSVariable variable)
                return variables.computeIfAbsent(variable, var -> SMTLIBIntVariable.create(var.getName()));

            var functionApplication = (TRSFunctionApplication) term;
            var cachedVariables = functionCoefficients.computeIfAbsent(
                    functionApplication.getFunctionSymbol(),
                    f -> IntStream.rangeClosed(1, f.getArity()) // TODO: rangeClosed(0, arity)
                            .mapToObj(i -> SMTLIBIntVariable.create(f.getName() + i))
                            .toList()
            );

            List<SMTLIBIntValue> summands = new LinkedList<>();
            summands.add(SMTLIBIntConstant.create(BigInteger.ONE));

            for (int i = 0; i < functionApplication.getArity(); i++) {
                var functionCoefficient = cachedVariables.get(i);
                var argumentCoefficient = encodeTerm(functionApplication.getArgument(i));
                summands.add(SMTLIBIntMult.create(List.of(functionCoefficient, argumentCoefficient)));
            }

            return SMTLIBIntPlus.create(summands);
        }

        private Set<Rule> computeUsableRules(Set<Rule> rules, TRSTerm term) {
            if (!(term instanceof TRSFunctionApplication f))
                return Collections.emptySet();

            Set<Rule> usableRules = new HashSet<>();
            Set<Rule> unusableRules = new HashSet<>();
            var fng = new FreshNameGenerator(f.getVariables(), FreshNameGenerator.VARIABLES);

            computeUsableRulesSingleStep(ImmutableCreator.create(rules), f, usableRules, unusableRules, fng);

            // Only currently unused rules can become used
            boolean anyRuleAdded = false;
            do {
                ImmutableSet<Rule> currentUnusableRules = ImmutableCreator.create(new HashSet<>(unusableRules));
                for (var rule : currentUnusableRules) {
                    if (!(rule.getRight() instanceof TRSFunctionApplication g))
                        break;
                    anyRuleAdded = computeUsableRulesSingleStep(currentUnusableRules, g, usableRules, unusableRules, fng);
                    if (anyRuleAdded)
                        break;
                }
            } while (anyRuleAdded);

            return usableRules;
        }

        private static boolean computeUsableRulesSingleStep(ImmutableSet<Rule> currentlyUnusedRules, TRSFunctionApplication f, Set<Rule> usableRules, Set<Rule> unusableRules, FreshNameGenerator fng) {
            boolean anyRuleAdded = false;
            for (var rule : currentlyUnusedRules) {
                var tcapArgs = f.getArguments().stream().map(arg -> arg.tcap(ImmutableCreator.create(arg.getFunctionSymbols()), fng)).toList();
                var fPrime = TRSTerm.createFunctionApplication(f.getFunctionSymbol(), tcapArgs);
                if (fPrime.unifies(rule.getLeft()) && usableRules.add(rule)) {
                    unusableRules.remove(rule);
                    anyRuleAdded = true;
                } else {
                    unusableRules.add(rule);
                }
            }

            return anyRuleAdded;
        }
    }
}
