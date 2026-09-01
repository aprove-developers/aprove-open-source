package aprove.verification.confluence;

import aprove.prooftree.Obligations.BasicObligation;
import aprove.prooftree.Obligations.BasicObligationNode;
import aprove.solver.Engines.SMTEngine;
import aprove.solver.Engines.SMTLIBEngine;
import aprove.solver.Engines.WrongLogicException;
import aprove.solver.SolverFactory;
import aprove.strategies.Abortions.Abortion;
import aprove.strategies.Abortions.AbortionException;
import aprove.strategies.Annotations.ParamsViaArgumentObject;
import aprove.strategies.ExecutableStrategies.RuntimeInformation;
import aprove.verification.confluence.Utility.CriticalPairInfo;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.Orders.POLO;
import aprove.verification.dpframework.Processor;
import aprove.verification.dpframework.Result;
import aprove.verification.dpframework.ResultFactory;
import aprove.verification.oldframework.Algebra.Polynomials.ConstraintType;
import aprove.verification.oldframework.Algebra.Polynomials.SimplePolynomial;
import aprove.verification.oldframework.BasicStructures.FunctionSymbol;
import aprove.verification.oldframework.Logic.YNM;
import aprove.verification.oldframework.PropositionalLogic.Formula;
import aprove.verification.oldframework.PropositionalLogic.FormulaFactory;
import aprove.verification.oldframework.PropositionalLogic.Formulae.NonCountingCircuitFactory;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.SMTLIBIntEquals;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntConstant;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntFunctions.SMTLIBIntMod;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBTheoryAtom;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.Diophantine;
import aprove.verification.oldframework.Utility.FreshNameGenerator;
import immutables.ImmutableCreator;

import java.math.BigInteger;
import java.util.*;
import java.util.stream.Collectors;
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
        if (oneStepUnfolding.size() > arguments.MaxNumberOfUnfoldedRules)
            return ResultFactory.unsuccessful();

        var fng = new FreshNameGenerator(FreshNameGenerator.VARIABLES);
        var newConfTrsProblem = ConfTRSProblem.create(ImmutableCreator.create(oneStepUnfolding));
        var candidates = newConfTrsProblem.getCriticalPairs().getAllFoundCriticalPairs(aborter)
                .stream()
                .filter(cpInfo -> !cpInfo.isTrivial())
                .map(cpInfo -> ground(cpInfo, fng))
                .sorted(Comparator.comparingInt((CriticalPairInfo cpInfo) -> (cpInfo.s().getSize() + cpInfo.t().getSize())))
                .toList();

        int limit = arguments.MaxNumberOfCriticalPairs;
        for (var candidate : candidates) {
            if (limit <= 0)
                break;

            var state = new PolynomialInterpretationNonConfluenceProcessorState(arguments, confTrsProblem, smtEngine, aborter);

            var interpretation = state.disproveByPolynomialInterpretation(candidate.s(), candidate.t());
            if (interpretation != null)
                return ResultFactory.disproved(new NotCRProof(candidate.divergence(), candidate.s(), candidate.t()));

            var polynomialOrder = state.disproveByOrdering(candidate.s(), candidate.t());
            if (polynomialOrder != null)
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
        public SolverFactory Order;
        public int MaxNumberOfCriticalPairs = 100;
        public int MaxNumberOfUnfoldedRules = 1000;
        public int Modulus = 3;
    }

    public CriticalPairInfo ground(CriticalPairInfo cpInfo, FreshNameGenerator fng) {
        var variables = new HashSet<TRSVariable>();
        variables.addAll(cpInfo.divergence().getVariables());
        variables.addAll(cpInfo.s().getVariables());
        variables.addAll(cpInfo.t().getVariables());
        if (variables.isEmpty())
            return cpInfo;

        var substitutionMap = new LinkedHashMap<TRSVariable, TRSFunctionApplication>();
        for (var v : variables) {
            var constantName = fng.getFreshName("c_" + v.getName(), false);
            var constant = TRSFunctionApplication.createConstant(constantName);
            substitutionMap.putIfAbsent(v, constant);
        }

        var substitution = TRSSubstitution.create(ImmutableCreator.create(substitutionMap));
        var newDivergence = cpInfo.divergence().applySubstitution(substitution);
        var newS = cpInfo.s().applySubstitution(substitution);
        var newT = cpInfo.t().applySubstitution(substitution);
        return new CriticalPairInfo(cpInfo.sRule(), cpInfo.tRule(), newS, newT, cpInfo.isRootOverlap(), newDivergence, cpInfo.p());
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

    private record LinearPolynomial(SimplePolynomial constantPart, Map<TRSVariable, SimplePolynomial> coefficientsForVariable) {
        public LinearPolynomial plus(LinearPolynomial other) {
                var newConstantPart = constantPart.plus(other.constantPart);
                var newCoefficientsForVariables = new LinkedHashMap<TRSVariable, SimplePolynomial>(coefficientsForVariable.size());
                for (var entry : coefficientsForVariable.entrySet()) {
                    var otherValue = other.coefficientsForVariable.getOrDefault(entry.getKey(), SimplePolynomial.ZERO);
                    newCoefficientsForVariables.put(entry.getKey(), entry.getValue().plus(otherValue));
                }

                other.coefficientsForVariable.forEach(newCoefficientsForVariables::putIfAbsent);
                return new LinearPolynomial(newConstantPart, newCoefficientsForVariables);
            }

            public LinearPolynomial minus(LinearPolynomial other) {
                var newConstantPart = constantPart.minus(other.constantPart);
                var newCoefficientsForVariables = new LinkedHashMap<TRSVariable, SimplePolynomial>(coefficientsForVariable.size());
                for (var entry : coefficientsForVariable.entrySet()) {
                    var otherValue = other.coefficientsForVariable.getOrDefault(entry.getKey(), SimplePolynomial.ZERO);
                    newCoefficientsForVariables.put(entry.getKey(), entry.getValue().minus(otherValue));
                }

                other.coefficientsForVariable.forEach((variable, coefficient) ->
                        newCoefficientsForVariables.putIfAbsent(variable, coefficient.negate()));
                return new LinearPolynomial(newConstantPart, newCoefficientsForVariables);
            }

            public LinearPolynomial times(SimplePolynomial functionCoefficient) {
                var newConstantPart = constantPart.times(functionCoefficient);
                var newCoefficientsForVariables = new LinkedHashMap<TRSVariable, SimplePolynomial>(coefficientsForVariable.size());
                for (var entry : coefficientsForVariable.entrySet()) {
                    var newCoefficient = entry.getValue().times(functionCoefficient);
                    newCoefficientsForVariables.put(entry.getKey(), newCoefficient);
                }

                return new LinearPolynomial(newConstantPart, newCoefficientsForVariables);
            }
        }

    private static class PolynomialInterpretationNonConfluenceProcessorState {
        private final Arguments arguments;
        private final Set<Rule> renamedRules;
        private final Set<FunctionSymbol> functionSymbols;
        private final SMTEngine smtEngine;
        private final Abortion aborter;
        private final FormulaFactory<SMTLIBTheoryAtom> ff = new NonCountingCircuitFactory<>();
        private final FormulaFactory<Diophantine> dff = new NonCountingCircuitFactory<>();
        private final Map<FunctionSymbol, List<SimplePolynomial>> functionCoefficients = new LinkedHashMap<>();

        private final SMTLIBIntConstant zero = SMTLIBIntConstant.create(BigInteger.ZERO);
        private final SMTLIBIntConstant modulus;

        private PolynomialInterpretationNonConfluenceProcessorState(Arguments arguments, ConfTRSProblem confTRSProblem, SMTEngine smtEngine, Abortion aborter) {
            this.arguments = arguments;
            var rules = confTRSProblem.getRules();
            var forbiddenVars = rules.stream().flatMap(rr -> rr.getVariables().stream()).collect(Collectors.toSet());
            this.renamedRules = rules.stream().map(r -> {
                var renamedRule = r.renameVariables(forbiddenVars);
                forbiddenVars.addAll(renamedRule.getVariables());
                return renamedRule;
            }).collect(Collectors.toSet());
            this.functionSymbols = confTRSProblem.getDefinedSymbolsOfR();
            this.smtEngine = smtEngine;
            this.aborter = aborter;
            this.modulus = SMTLIBIntConstant.create(BigInteger.valueOf(arguments.Modulus));
        }

        private Map<String, String> disproveByPolynomialInterpretation(TRSTerm s, TRSTerm t) {
            var usableRules = computeUsableRules(renamedRules, s);
            usableRules.addAll(computeUsableRules(renamedRules, t));
            List<SMTLIBTheoryAtom> rulesEqualZeroModK = new LinkedList<>();

            var sEncoding = encodeTerm(s);
            var tEncoding = encodeTerm(t);
            var sMinusT = sEncoding.minus(tEncoding);
            var sMinusTModK = SMTLIBIntMod.create(List.of(sMinusT.constantPart().toSMTLIB(), modulus));
            var sEqualsTModKEqualsZero = SMTLIBIntEquals.create(sMinusTModK, zero);

            for (var rule : usableRules) {
                var lhs = encodeTerm(rule.getLeft());
                var rhs = encodeTerm(rule.getRight());
                var lhsMinusRhs = lhs.minus(rhs);
                var constantPartModK = SMTLIBIntMod.create(List.of(lhsMinusRhs.constantPart().toSMTLIB(), modulus));
                rulesEqualZeroModK.add(SMTLIBIntEquals.create(constantPartModK, zero));
                for (var coefficients : lhsMinusRhs.coefficientsForVariable().values()) {
                    var coefficientModK = SMTLIBIntMod.create(List.of(coefficients.toSMTLIB(), modulus));
                    rulesEqualZeroModK.add(SMTLIBIntEquals.create(coefficientModK, zero));
                }
            }

            var searchSpaceValues = IntStream.range(0, arguments.Modulus).mapToObj(i -> SMTLIBIntConstant.create(BigInteger.valueOf(i))).toList();
            List<Formula<SMTLIBTheoryAtom>> searchSpaceConstraints = functionCoefficients.values()
                    .stream()
                    .flatMap(Collection::stream)
                    .map(var -> searchSpaceValues.stream().map(value -> (Formula<SMTLIBTheoryAtom>) ff.buildTheoryAtom(SMTLIBIntEquals.create(var.toSMTLIB(), value))).toList())
                    .map(ff::buildOr)
                    .toList();
            List<Formula<SMTLIBTheoryAtom>> constraints = new LinkedList<>(searchSpaceConstraints);
            Formula<SMTLIBTheoryAtom> notSEqualsTModK = ff.buildNot(ff.buildTheoryAtom(sEqualsTModKEqualsZero));
            constraints.add(notSEqualsTModK);
            constraints.addAll(ff.buildTheoryAtoms(rulesEqualZeroModK));

            try {
                var result = smtEngine.solve(constraints, SMTEngine.SMTLogic.QF_NIA, aborter);
                if (result.x == YNM.YES)
                    return result.y;
                return null;
            } catch (WrongLogicException e) {
                return null;
            }
        }

        private POLO disproveByOrdering(TRSTerm s, TRSTerm t) {
            var usableRulesS = computeUsableRules(renamedRules, s);
            var usableRulesT = computeUsableRules(renamedRules, t);

            var result = disproveByOrderingDirected(s, t, usableRulesS, usableRulesT);
            if (result == null)
                result = disproveByOrderingDirected(t, s, usableRulesT, usableRulesS);

            return result;
        }

        private void addConstraints(LinearPolynomial encodedTerm, ConstraintType constraintType, List<Diophantine> constraints) {
            var constantConstraint = Diophantine.create(encodedTerm.constantPart(), constraintType);
            constraints.add(constantConstraint);
            for (var coefficient : encodedTerm.coefficientsForVariable().values()) {
                var coefficientGreaterEqualsZero = Diophantine.create(coefficient, ConstraintType.GE);
                constraints.add(coefficientGreaterEqualsZero);
            }
        }

        private POLO disproveByOrderingDirected(TRSTerm high, TRSTerm low, Set<Rule> highUsableRules, Set<Rule> lowUsableRules) {
            List<Diophantine> constraints = new LinkedList<>();

            // [[l]] >= [[r]] for all l -> r in U_r(R, low)
            for (var highRule : highUsableRules) {
                var lhs = encodeTerm(highRule.getLeft());
                var rhs = encodeTerm(highRule.getRight());
                var rhsMinusLhs = rhs.minus(lhs);
                addConstraints(rhsMinusLhs, ConstraintType.GE, constraints);
            }

            // [[l]] <= [[r]] for all l -> r in U_r(R, high)
            for (var lowRule : lowUsableRules) {
                var lhs = encodeTerm(lowRule.getLeft());
                var rhs = encodeTerm(lowRule.getRight());
                var lhsMinusRhs = lhs.minus(rhs);
                addConstraints(lhsMinusRhs, ConstraintType.GE, constraints);
            }

            // [[high]] > [[low]]
            var highEncoding = encodeTerm(high);
            var lowEncoding = encodeTerm(low);
            var highMinusLow = highEncoding.minus(lowEncoding);
            addConstraints(highMinusLow, ConstraintType.GT, constraints);

            constraints.addAll(functionCoefficients.values().stream().flatMap(List::stream).map(coefficients -> Diophantine.create(coefficients, ConstraintType.GE)).toList());
            var conjunction = dff.buildAnd(dff.buildTheoryAtoms(constraints));
            var poloSolver = arguments.Order.getPOLOSolver(functionSymbols, aborter);
            return poloSolver.solveDioFormula(conjunction, aborter);
        }

        private LinearPolynomial encodeTerm(TRSTerm term) {
            if (term instanceof TRSVariable variable) {
                var coefficientsForArguments = new LinkedHashMap<TRSVariable, SimplePolynomial>();
                coefficientsForArguments.put(variable, SimplePolynomial.ONE);
                return new LinearPolynomial(SimplePolynomial.ZERO, coefficientsForArguments);
            }

            var functionApplication = (TRSFunctionApplication) term;
            var coefficients = functionCoefficients.computeIfAbsent(
                    functionApplication.getFunctionSymbol(),
                    f -> IntStream.rangeClosed(0, f.getArity())
                            .mapToObj(i -> SimplePolynomial.create("a_" + f.getName() + "," + i))
                            .toList()
            );

            var result = new LinearPolynomial(coefficients.getFirst(), new LinkedHashMap<>());

            // a_f,i+1 * encode(arg_i(term)) for 0 <= i < f.arity
            // We ignore the constant term a_f,0
            for (int i = 0; i < functionApplication.getArity(); i++) {
                var functionCoefficient = coefficients.get(i+1);
                var argumentCoefficient = encodeTerm(functionApplication.getArgument(i));
                result = result.plus(argumentCoefficient.times(functionCoefficient));
            }

            return result;
        }

        private Set<Rule> computeUsableRules(Set<Rule> rules, TRSTerm term) {
            if (!(term instanceof TRSFunctionApplication f))
                return Collections.emptySet();

            var definedSymbols = ImmutableCreator.create(new IncrementalRuleMap(rules).getDefinedSymbols());
            Set<Rule> usableRules = new HashSet<>();
            Set<Rule> unusableRules = new HashSet<>(rules);
            var fng = new FreshNameGenerator(f.getVariables(), FreshNameGenerator.VARIABLES);

            Deque<TRSTerm> worklist = new ArrayDeque<>();
            worklist.add(term);
            Set<TRSTerm> scanned = new HashSet<>();

            while (!worklist.isEmpty()) {
                TRSTerm current = worklist.poll();
                if (!scanned.add(current))
                    continue;

                Set<TRSFunctionApplication> subterms = current.getNonVariableSubTerms();

                for (var sub : subterms) {
                    var cappedArgs = sub.getArguments().stream()
                            .map(arg -> arg.tcap(definedSymbols, fng))
                            .toList();
                    var capped = TRSTerm.createFunctionApplication(sub.getFunctionSymbol(), cappedArgs);

                    for (Iterator<Rule> iterator = unusableRules.iterator(); iterator.hasNext(); ) {
                        Rule rule = iterator.next();
                        if (capped.unifies(rule.getLeft())) {
                            iterator.remove();
                            usableRules.add(rule);
                            worklist.add(rule.getRight());
                        }
                    }
                }
            }

            return usableRules;
        }
    }
}
