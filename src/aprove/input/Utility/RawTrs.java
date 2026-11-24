package aprove.input.Utility;

import static java.util.stream.Collectors.*;

import java.util.*;

import aprove.runtime.*;
import aprove.verification.complexity.TruthValue.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import immutables.*;

public class RawTrs {
    private final Set<TRSVariable> variables = new LinkedHashSet<TRSVariable>();
    private Set<Rule> pairs = null;
    private final Map<Integer, Rule> pairNums =
        new LinkedHashMap<Integer, Rule>();
    private Set<Pair<Integer, Integer>> edges = null;
    private boolean complexity = false;
    private boolean constructorbased = false;
    private boolean innermost = false;
    private boolean outermost = false;
    private boolean parallelInnermost = false;
    private boolean minimal = false;
    private Set<Rule> rules = null;
    private final Set<GeneralizedRule> allRules =
        new LinkedHashSet<GeneralizedRule>();
    private final Set<Pair<TRSTerm,TRSTerm>> lhsVariableRules =
            new LinkedHashSet<Pair<TRSTerm,TRSTerm>>();
    private Set<Pair<String, Set<Integer>>> replacementMap =
        new LinkedHashSet<Pair<String, Set<Integer>>>();
    private final Set<ConditionalRule> condrules =
        new LinkedHashSet<ConditionalRule>();
    private Set<String> associativeNames = new LinkedHashSet<String>();
    private Set<String> commutativeNames = new LinkedHashSet<String>();
    private Set<String> associativeAndCommutativeNames =
        new LinkedHashSet<String>();
    private Set<Rule> relativeRules = new LinkedHashSet<Rule>();
    private final Set<Equation> equations = new LinkedHashSet<Equation>();
    private Set<ProbabilisticRule> probabilisticRules = null;
    private Map<String, Integer> arityMap =
        new LinkedHashMap<String, Integer>();
    // TODO what to do with this status value?
    private ComplexityYNM status;
    private Map<FunctionSymbol, PredefinedFunction<? extends Domain>> predefinedFunctionSemantics =
        new LinkedHashMap<FunctionSymbol, PredefinedFunction<? extends Domain>>();
    private Map<FunctionSymbol, Domain> domainSemantics =
        new LinkedHashMap<FunctionSymbol, Domain>();
    private Set<TRSFunctionApplication> q = null;

    public Set<TRSVariable> getVariables() {
        return this.variables;
    }

    public boolean isVariable(String sym) {
        return this.variables.stream().map(x -> x.getName()).collect(toSet()).contains(sym);
    }

    public boolean isComplexity() {
        return this.complexity;
    }

    public boolean isConstructorbased() {
        return this.constructorbased;
    }

    public Set<Rule> getSimpleRules() {
        return this.rules;
    }

    public Set<GeneralizedRule> getAllRules() {
        return this.allRules;
    }
    
    public Set<Pair<TRSTerm,TRSTerm>> getAllLHSVariableRules() {
        return this.lhsVariableRules;
    }

    public Set<TRSFunctionApplication> getQFunctionApplications() {
        return this.q;
    }

    public Set<TRSFunctionApplication> getInitialTerms() {
        // TODO Auto-generated method stub
        return null;
    }

    /**
     * @return the explicitly given equations, e.g., from
     *         <code>(THEORY (EQUATIONS l == r ...))</code>, that are neither an
     *         A- nor a C-equation (see {@link #addEquation(TRSTerm, TRSTerm)}).
     *         Equations of named theories (A, C, AC) are not contained here.
     */
    public Set<Equation> getEquations() {
        return this.equations;
    }

    public Set<Rule> getRelativeRules() {
        return this.relativeRules;
    }

    public Set<ProbabilisticRule> getProbabilisticRules() {
        return this.probabilisticRules;
    }

    public Set<ConditionalRule> getConditionalRules() {
        return this.condrules;
    }

    public Set<ConditionalRule> getGeneralizedConditionalRules() {
        // TODO Auto-generated method stub
        return null;
    }

    public Set<Pair<String, Set<Integer>>> getContextSensitiveRules() {
        if (this.replacementMap.isEmpty()) {
            return null;
        }
        return this.replacementMap;
    }

    public Set<Rule> getPairs() {
        return this.pairs;
    }

    public boolean getInnermost() {
        return this.innermost;
    }

    public boolean getOutermost() {
        return this.outermost;
    }

    public boolean getParellelInnermost() {
        return this.parallelInnermost;
    }

    public void setComplexity(boolean complexity) {
        this.complexity = complexity;
    }

    public void setConstructorbased(boolean constructorbased) {
        this.constructorbased = constructorbased;
    }

    public void setMinimal(boolean minimal) {
        this.minimal = minimal;
    }

    public boolean getMinimal() {
        return this.minimal;
    }

    public Set<String> getAssociativeFunctionSymbols() {
        return this.associativeNames;
    }

    public Set<String> getCommutativeFunctionSymbols() {
        return this.commutativeNames;
    }

    public Set<String> getAssAndCommFunctionSymbols() {
        return this.associativeAndCommutativeNames;
    }

    public void addVariable(TRSVariable x) {
        this.variables.add(x);
    }

    public void addSimpleRule(Rule r) {
        if (this.rules == null) {
            this.rules = new LinkedHashSet<Rule>();
        }
        this.rules.add(r);
        this.allRules.add(r);
    }

    public void addGeneralizedRule(GeneralizedRule r) {
        this.allRules.add(r);
    }
    
    public void addLHSVariableRule(TRSTerm l, TRSTerm r) {
        this.lhsVariableRules.add(new Pair<TRSTerm,TRSTerm>(l,r));
    }

    public void setOutermost(boolean b) {
        this.outermost = b;
    }

    public void setInnermost(boolean b) {
        this.innermost = b;
    }

    public void setParallelInnermost(boolean b) {
        this.parallelInnermost = b;
    }

    public void setReplacementMap(Set<Pair<String, Set<Integer>>> replacementMap) {
        this.replacementMap = replacementMap;
    }

    public void addConditionalRule(ConditionalRule condrule) {
        this.condrules.add(condrule);
    }

    public void addAssociativeName(String name) {
        this.associativeNames.add(name);
    }

    public void addCommutativeName(String name) {
        this.commutativeNames.add(name);
    }

    public void addAssociativeAndCommutativeName(String name) {
        this.associativeAndCommutativeNames.add(name);
    }

    public void addRelativeRule(Rule r) {
        this.relativeRules.add(r);
    }

    /**
     * Adds an explicitly given equation <code>lhs == rhs</code>. Equations
     * that are an associativity (A) or commutativity (C) equation for some
     * binary symbol f are stored like the named theories <code>(A f)</code>
     * and <code>(C f)</code> (both together yield AC), because the ETRS
     * techniques rely on the standard orientation of these equations that
     * the named theories produce (see OblCreatorEtrs). All other equations
     * are kept as they are; they are rejected when creating the obligation.
     */
    public void addEquation(TRSTerm lhs, TRSTerm rhs) {
        Equation equation = Equation.create(lhs, rhs);
        if (equation.checkAEquation()) {
            this.addAssociativeName(((TRSFunctionApplication) lhs).getRootSymbol().getName());
        } else if (equation.checkCEquation()) {
            this.addCommutativeName(((TRSFunctionApplication) lhs).getRootSymbol().getName());
        } else {
            this.equations.add(equation);
        }
    }

    public void addReplacementMapEntry(String name, Set<Integer> replacements) {
        this.replacementMap.add(new Pair<String, Set<Integer>>(name,
            replacements));
    }

    public void addArityMapEntry(String name, int arity) {
        this.arityMap.put(name, arity);
    }

    public void setStatus(ComplexityYNM status) {
        this.status = status;
    }

    public void addPredefinedFunctionSemantics(FunctionSymbol sym,
            PredefinedFunction<? extends Domain> sem) {
        this.predefinedFunctionSemantics.put(sym, sem);
    }

    public Map<FunctionSymbol, PredefinedFunction<? extends Domain>> getPredefinedFunctionSemantics() {
        return this.predefinedFunctionSemantics;
    }

    public void addDomainSemantics(FunctionSymbol sym, Domain dom) {
        this.domainSemantics.put(sym, dom);
    }

    public Map<FunctionSymbol, Domain> getDomainSemantics() {
        return this.domainSemantics;
    }

    public void addPair(Rule pair) {
        if (this.pairs == null) {
            this.pairs = new LinkedHashSet<Rule>();
        }
        this.pairs.add(pair);
        Integer num = this.pairs.size();
        this.pairNums.put(num, pair);
    }

    public Set<Pair<Integer, Integer>> getEdges() {
        return this.edges;
    }

    public void addAbstractRule(TRSTerm lhs,
            TRSTerm rhs,
            List<Condition> conditions,
            boolean relative,
            boolean pair) {
        Set<TRSVariable> lhsvars = lhs.getVariables();
        Set<TRSVariable> rhsvars = rhs.getVariables();
        if (conditions.isEmpty()) {
            if (!lhs.isVariable()) {
                if (lhsvars.containsAll(rhsvars)) {
                    Rule r = Rule.create((TRSFunctionApplication) lhs, rhs);
                    if (relative) {
                        if (pair) {
                            throw new UnhandledConstructException(
                                "relative pairs");
                        }
                        this.addRelativeRule(r);
                    } else {
                        if (pair) {
                            this.addPair(r);
                        } else {
                            this.addSimpleRule(r);
                        }
                    }
                } else {
                    if (relative) {
                        throw new UnhandledConstructException(
                            "relative rules/pairs that violate the variable condition");
                    } else {
                        if (pair) {
                            throw new UnhandledConstructException(
                                "pairs that violate the variable condition");
                        }
                        GeneralizedRule r = GeneralizedRule.create((TRSFunctionApplication) lhs, rhs);
                        this.addGeneralizedRule(r);
                    }
                }
            } else {
                if (pair) {
                    throw new UnhandledConstructException(
                        "pairs with variables as lhs");
                }
                if (relative) {
                    if (lhsvars.containsAll(rhsvars) && Options.certifier.isNone()) {
                        this.addLHSVariableRule(lhs, rhs);
                    } else {
                        throw new UnhandledConstructException(
                            "rules that violate the variable condition");
                    }
                } else {
                    throw new UnhandledConstructException(
                        "(non-relative) rule with variables as lhs");
                }
            }
        } else {
            if (pair) {
                throw new UnhandledConstructException("pairs with conditions");
            }
            if (relative) {
                throw new UnhandledConstructException(
                    "conditional relative rules");
            }
            GeneralizedRule r =
                GeneralizedRule.create((TRSFunctionApplication) lhs, rhs);
            ImmutableList<Condition> conds =
                ImmutableCreator.create(conditions);
            ConditionalRule condrule = ConditionalRule.create(r, conds);
            this.addConditionalRule(condrule);
        }
    }

    public void addQTerm(TRSFunctionApplication t) {
        if (this.q == null) {
            this.q = new LinkedHashSet<TRSFunctionApplication>();
        }
        this.q.add(t);
    }

    public void hasQ() {
        if (this.q == null) {
            this.q = new LinkedHashSet<TRSFunctionApplication>();
        }
    }

    public void hasRules() {
        if (this.rules == null) {
            this.rules = new LinkedHashSet<Rule>();
        }
    }

    public void setEdges(Set<Pair<Integer, Integer>> edges) {
        this.edges = edges;
    }

    public void hasPairs() {
        if (this.pairs == null) {
            this.pairs = new LinkedHashSet<Rule>();
        }
    }
}
