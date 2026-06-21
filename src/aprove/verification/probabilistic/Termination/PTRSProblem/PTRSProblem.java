package aprove.verification.probabilistic.Termination.PTRSProblem;

import java.util.*;
import java.util.stream.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.LowerBounds.Types.*;
import aprove.verification.complexity.LowerBounds.Types.TypeInference.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Utility.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import immutables.*;

/**
 * @author J-C Kassing
 * @version $Id$
 */
public class PTRSProblem extends DefaultBasicObligation implements Immutable {

    // ================================================================================
    // Properties
    // ================================================================================

    private final ProbabilisticTerminationResult target;
    private final RewriteStrategy strat;
    private final boolean basic;

    private final Set<ProbabilisticRule> PR;

    /* Computed Values */
    private volatile CriticalPairs critPairs;
    private final ImmutableSet<FunctionSymbol> signature;
    private volatile ImmutableSet<FunctionSymbol> defSymbolsOfR;
    private volatile ImmutableSet<FunctionSymbol> constructorsOfR;
    private volatile ImmutableMap<FunctionSymbol, ImmutableSet<ProbabilisticRule>> ruleMap;

    private final int hashCode;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    public PTRSProblem(final Set<ProbabilisticRule> probabilisticRules,
        final RewriteStrategy strat,
        final ProbabilisticTerminationResult target,
        final boolean basic) {
        super("PTRS", "Probabilistic TRS");

        this.PR = probabilisticRules;
        this.strat = strat;
        this.target = target;
        this.basic = basic;
        this.critPairs = null;
        this.defSymbolsOfR = null;
        this.ruleMap = null;
        final Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.PR);
        this.signature = ImmutableCreator.create(signature);
        this.hashCode = Objects.hash(this.PR);

        calculateDefSymbolsAndRuleMap();
    }

    public PTRSProblem(final ImmutableSet<ProbabilisticRule> probabilisticRules,
        final RewriteStrategy strat,
        final ProbabilisticTerminationResult target,
        final boolean basic) {
        super("PTRS", "Probabilistic TRS");

        this.PR = probabilisticRules;
        this.strat = strat;
        this.target = target;
        this.basic = basic;
        this.critPairs = null;
        this.defSymbolsOfR = null;
        this.ruleMap = null;
        final Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.PR);
        this.signature = ImmutableCreator.create(signature);
        this.hashCode = Objects.hash(this.PR);

        calculateDefSymbolsAndRuleMap();
    }

    /**
     * creates a new PTRS-Problem for the given collection of Rules
     * @param PR the probabilistic rules
     */
    public static PTRSProblem create(final ImmutableSet<ProbabilisticRule> PR,
        final RewriteStrategy strat,
        final ProbabilisticTerminationResult target,
        final boolean basic) {
        return new PTRSProblem(PR, strat, target, basic);
    }

    // ================================================================================
    // Accessors
    // ================================================================================

    public Set<ProbabilisticRule> getProbabilisticRules() {
        return this.PR;
    }

    public Set<ProbabilisticRule> getPR() {
        return this.PR;
    }

    public boolean isInnermost() {
        return this.strat == RewriteStrategy.INNERMOST || this.strat == RewriteStrategy.PARALLEL_SIMULTANEOUS_INNERMOST;
    }

    public boolean isOutermost() {
        return this.strat == RewriteStrategy.OUTERMOST || this.strat == RewriteStrategy.PARALLEL_SIMULTANEOUS_OUTERMOST;
    }

    public boolean isBasic() {
        return this.basic;
    }

    public RewriteStrategy getRewriteStrategy() {
        return this.strat;
    }

    public ProbabilisticTerminationResult getTarget() {
        return this.target;
    }

    public ImmutableSet<FunctionSymbol> getSignature() {
        return this.signature;
    }

    public ImmutableSet<FunctionSymbol> getDefSymbolsOfR() {
        return this.defSymbolsOfR;
    }

    public ImmutableMap<FunctionSymbol, ImmutableSet<ProbabilisticRule>> getRuleMap() {
        return this.ruleMap;
    }

    private void calculateDefSymbolsAndRuleMap() {
        final Map<FunctionSymbol, Set<ProbabilisticRule>> ruleMap =
            new LinkedHashMap<>();
        for (final ProbabilisticRule rule : this.PR) {
            final FunctionSymbol f = rule.getRootSymbol();
            Set<ProbabilisticRule> fRules = ruleMap.get(f);
            if (fRules == null) {
                fRules = new LinkedHashSet<>();
                ruleMap.put(f, fRules);
            }
            fRules.add(rule);
        }
        // make immutable
        final Map<FunctionSymbol, ImmutableSet<ProbabilisticRule>> immutableMap =
            new LinkedHashMap<>();
        for (final Map.Entry<FunctionSymbol, Set<ProbabilisticRule>> entry : ruleMap.entrySet()) {
            immutableMap.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
        }

        this.ruleMap = ImmutableCreator.create(immutableMap);
        this.defSymbolsOfR = ImmutableCreator.create(immutableMap.keySet());

        final Set<FunctionSymbol> constructors = new HashSet<>();
        for (final var f : getSignature()) {
            if (!this.defSymbolsOfR.contains(f)) {
                constructors.add(f);
            }
        }
        this.constructorsOfR = ImmutableCreator.create(constructors);
    }

    /** Returns true, if this PTRS is a normal TRS, i.e. every probabilistic rules has the form l -> {1:r}. */
    public boolean isNonProbabilistic() {
        for (final ProbabilisticRule pr : this.PR) {
            if (!pr.isDeterministic()) {
                return false;
            }
        }
        return true;
    }

    /**
     * Returns the non-probabilistic abstraction np(S) of this PTRS.
     * Ignores the rewrite strategy and creates an empty set Q.
     * @return
     */
    public QTRSProblem getNonProbAbstraction() {
        final HashSet<Rule> allNonProbRules = new HashSet<>();
        for (final ProbabilisticRule pr : this.PR) {
            allNonProbRules.addAll(pr.getNonProbabilisticRepresentation());
        }
        return QTRSProblem.create(ImmutableCreator.create(allNonProbRules));
    }

    //TODO Create correct critical pairs if needed one day and remove this hack.
    /**
     * Returns the non-probabilistic l-abstraction np_l(S) of this PTRS.
     * This is the same as np(S) but for each rule l -> {p_1:r_1, ..., p_k:r_k}
     * we create only one rule l -> freshSymbol.
     * (used to check for critical pairs but not to compute them!)
     * Ignores the rewrite strategy and creates an empty set Q.
     * @return
     */
    public QTRSProblem getNonProbLAbstraction() {
        // first copy the original signature
        final FunctionSymbolGenerator funSymGen = new FunctionSymbolGenerator(this.signature.size() + this.PR.size());

        for (final FunctionSymbol f : this.signature) {
            final FunctionSymbol g = funSymGen.getFresh(f.getName(),
                f
                    .getArity());
            if (Globals.useAssertions) {
                assert (f.equals(g));
            }
        }
        final HashSet<Rule> allNonProbLRules = new HashSet<>();
        for (final ProbabilisticRule pr : this.PR) {
            final FunctionSymbol g = funSymGen.getFresh("fresh", 0);
            allNonProbLRules.add(Rule.create(pr.getLeft(), TRSTerm.createFunctionApplication(g)));
        }
        return QTRSProblem.create(ImmutableCreator.create(allNonProbLRules));
    }
    
    public boolean isNonOverlapping() {
        return getCriticalPairs().isNonOverlapping(AbortionFactory.create());
    }

    public boolean isDuplicating() {
        for (final ProbabilisticRule rule : getPR()) {
            if (!rule.isDuplicating()) {
                return true;
            }
        }
        return false;
    }

    public Set<TRSVariable> getVariables() {
        final Set<TRSVariable> res = new HashSet<>();
        for (final ProbabilisticRule rule : getPR()) {
            res.addAll(rule.getLeft().getVariables());
            for (final TRSTerm term : rule.getRight().getSupport()) {
                res.addAll(term.getVariables());
            }
        }
        return res;
    }

    public boolean isRightGround() {
        for (final ProbabilisticRule rule : getPR()) {
            for (final TRSTerm term : rule.getRight().getSupport()) {
                if (!term.getVariables().isEmpty()) {
                    return false;
                }
            }
        }
        return true;
    }
    
    public boolean isGround() {
        return this.getVariables().isEmpty();
    }

    public boolean isVariableOccDecreasing() {
        for (final ProbabilisticRule rule : getPR()) {
            if (!rule.isVariableOccDecreasing()) {
                return true;
            }
        }
        return false;
    }

    public boolean isLeftLinear() {
        for (final ProbabilisticRule rule : getPR()) {
            if (!rule.isLeftLinear()) {
                return false;
            }
        }
        return true;
    }

    public boolean isRightLinear() {
        for (final ProbabilisticRule rule : getPR()) {
            for (final TRSTerm r : rule.getRight().getSupport()) {
                if (!r.isLinear()) {
                    return false;
                }
            }
        }
        return true;
    }

    public boolean isConstructorBased() {
        for (final ProbabilisticRule rule : getPR()) {
            final Set<FunctionSymbol> defsym = getDefSymbolsOfR();
            for (final TRSTerm argument : rule.getLeft().getArguments()) {
                for (final FunctionSymbol sym : argument.getFunctionSymbols()) {
                    if (defsym.contains(sym)) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    public boolean isTailRecursive() {
        for (final ProbabilisticRule rule : getPR()) {
            for (final TRSTerm r : rule.getRight().getSupport()) {
                final Set<TRSTerm> remainingSubTerms = new LinkedHashSet<>();
                remainingSubTerms.add(r);

                final Iterator<TRSTerm> iterator = remainingSubTerms.iterator();
                while (iterator.hasNext()) {
                    final TRSTerm t = iterator.next();
                    iterator.remove();
                    if (t instanceof TRSVariable) {
                        continue;
                    }
                    final TRSFunctionApplication currentTerm = (TRSFunctionApplication) t;
                    final FunctionSymbol currentRoot = currentTerm.getFunctionSymbol();

                    if (getDefSymbolsOfR().contains(currentRoot)) {
                        final Set<FunctionSymbol> functionSymbolsBelowDefinedSymbol = currentTerm.getFunctionSymbols();
                        functionSymbolsBelowDefinedSymbol.remove(currentTerm.getFunctionSymbol());

                        for (final FunctionSymbol s : functionSymbolsBelowDefinedSymbol) {
                            if (getDefSymbolsOfR().contains(s)) {
                                return false;
                            }
                        }
                    } else {
                        remainingSubTerms.addAll(currentTerm.getArguments());
                    }
                }
            }
        }
        return true;
    }

    /*
     * Only works when the PTRS is tail recursive!
     */
    public boolean isWeaklyNormalizing(final Set<ProbabilisticRule> remainingRules) throws Exception {
        if (!isTailRecursive()) {
            throw new Exception("only defined on tail-recursive PTRS");
        }
        boolean newRuleFound = false;
        do {
            newRuleFound = false;
            outer: for (final ProbabilisticRule rule : remainingRules) {
                for (final TRSTerm r : rule.getRight().getSupport()) {
                    if (r.isNormal(remainingRules)) {
                        newRuleFound = true;
                        remainingRules.remove(rule);
                        break outer;
                    }
                }
            }
        } while (newRuleFound);
        return remainingRules.isEmpty();
    }

    //TODO Fix this.
    /**
     * CURRENTLY ONLY BE USABLE TO CHECK IF CriticalPairs ARE EMPTY!
     * THE RESULTING CriticalPairs ARE NOT CONTAINING EVERYTHING THEY SHOULD!
     *
     * @return The set of critical pairs for this PQTRS
     */
    public CriticalPairs getCriticalPairs() {
        if (this.critPairs == null) {
            synchronized (this) {
                if (this.critPairs == null) {
                    this.critPairs = new CriticalPairs(getNonProbLAbstraction());
                }
            }
        }
        return this.critPairs;
    }

    public int getMaxVarNumberInRHS() {
        int res = 0;
        for (final ProbabilisticRule rule : getPR()) {
            for (final TRSTerm term : rule.getRight().getSupport()) {
                final Set<TRSVariable> variables = term.getVariables();
                final int maxEntry = variables.size();
                if (res < maxEntry) {
                    res = maxEntry;
                }
            }
        }
        return res;
    }

    public int getMaxVarCountInRHS() {
        int res = 0;
        for (final ProbabilisticRule rule : getPR()) {
            for (final TRSTerm term : rule.getRight().getSupport()) {
                final Map<TRSVariable, Integer> countVar = term.getVariableCount();
                if (!countVar.isEmpty()) {
                    final int maxEntry = countVar.entrySet()
                        .stream()
                        .max((e1, e2) -> e1.getValue()
                            .compareTo(e2.getValue()))
                        .get()
                        .getValue();
                    if (res < maxEntry) {
                        res = maxEntry;
                    }
                }
            }
        }
        return res;
    }

    /**
     * very simple fresh name generator
     */
    private static final class FunctionSymbolGenerator {

        private final Set<FunctionSymbol> fs;

        public FunctionSymbolGenerator(final int size) {
            this.fs = new HashSet<>(size);
        }

        public FunctionSymbol getFresh(final String name, final int arity) {
            int j = 0;
            String currentName = name;
            FunctionSymbol f;
            while (true) {
                f = FunctionSymbol.create(currentName, arity);
                if (this.fs.add(f)) {
                    return f;
                } else {
                    currentName = name + j;
                    j++;
                }
            }
        }

    }

    // ================================================================================
    // Utility
    // ================================================================================

    @Override
    public String getStrategyName() {
        return switch (this.target) {
            case certainTermination -> switch (this.strat) {
                case FULL -> "ptrs_TERM";
                case INNERMOST -> "ptrs_i_TERM";
                case OUTERMOST -> "ptrs_o_TERM";
                case PARALLEL_SIMULTANEOUS -> "ptrs_ps_TERM";
                case PARALLEL_SIMULTANEOUS_INNERMOST -> "ptrs_psi_TERM";
                case PARALLEL_SIMULTANEOUS_OUTERMOST -> "ptrs_pso_TERM";
                default -> "ptrs_TERM";
            };
            case AST -> switch (this.strat) {
                case FULL -> "ptrs_AST";
                case INNERMOST -> "ptrs_i_AST";
                case OUTERMOST -> "ptrs_o_AST";
                case PARALLEL_SIMULTANEOUS -> "ptrs_ps_AST";
                case PARALLEL_SIMULTANEOUS_INNERMOST -> "ptrs_psi_AST";
                case PARALLEL_SIMULTANEOUS_OUTERMOST -> "ptrs_pso_AST";
                default -> "ptrs_AST";
            };
            case SAST -> switch (this.strat) {
                case FULL -> "ptrs_SAST";
                case INNERMOST -> "ptrs_i_SAST";
                case OUTERMOST -> "ptrs_o_SAST";
                case PARALLEL_SIMULTANEOUS -> "ptrs_ps_SAST";
                case PARALLEL_SIMULTANEOUS_INNERMOST -> "ptrs_psi_SAST";
                case PARALLEL_SIMULTANEOUS_OUTERMOST -> "ptrs_pso_SAST";
                default -> "ptrs_SAST";
            };
            default -> "ptrs_TERM";
        };
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return switch (this.target) {
            case certainTermination -> switch (this.strat) {
                case FULL -> new DefaultProofPurposeDescriptor(this, "Termination");
                case INNERMOST -> new DefaultProofPurposeDescriptor(this, "Innermost Termination");
                case OUTERMOST -> new DefaultProofPurposeDescriptor(this, "Outermost Termination");
                default -> new DefaultProofPurposeDescriptor(this, "Termination");
            };
            case AST -> switch (this.strat) {
                case FULL -> new DefaultProofPurposeDescriptor(this, "AST");
                case INNERMOST -> new DefaultProofPurposeDescriptor(this, "Innermost AST");
                case OUTERMOST -> new DefaultProofPurposeDescriptor(this, "Outermost AST");
                default -> new DefaultProofPurposeDescriptor(this, "AST");
            };
            case SAST -> switch (this.strat) {
                case FULL -> new DefaultProofPurposeDescriptor(this, "SAST");
                case INNERMOST -> new DefaultProofPurposeDescriptor(this, "Innermost SAST");
                case OUTERMOST -> new DefaultProofPurposeDescriptor(this, "Outermost SAST");
                default -> new DefaultProofPurposeDescriptor(this, "SAST");
            };
            default -> new DefaultProofPurposeDescriptor(this, "Termination");
        };
    }

    @Override
    public String export(final Export_Util eu) {
        final StringBuilder s = new StringBuilder();
        s.append(eu.export("Probabilistic term rewrite system:"));
        s.append(eu.cond_linebreak());
        s.append(eu.export("The TRS has the following probabilistic rules:"));
        s.append(eu.cond_linebreak());
        s.append(eu.set(this.PR, Export_Util.RULES));
        s.append(eu.cond_linebreak());
        s.append(eu.export("and uses the " + this.strat.getRepresentation() + " rewrite strategy."));
        s.append(eu.cond_linebreak());

        return s.toString();
    }

    @Override
    public String toString() {
        return export(new PLAIN_Util());
    }

    @Override
    public boolean equals(final Object o) {
        if (this == o) {
            return true;
        }
        if (o == null || getClass() != o.getClass()) {
            return false;
        }
        final PTRSProblem that = (PTRSProblem) o;
        return this.hashCode == that.hashCode &&
            Objects.equals(this.PR, that.PR);
    }

    public ImmutableSet<FunctionSymbol> getConstructorsOfR() {
        return this.constructorsOfR;
    }

    public Optional<List<TRSTerm>> check(
        final List<ImmutableList<TRSTerm>> phi, // Pattern matrix
        final int n,							  // Number of patterns to match 	
        final List<Set<FunctionSymbol>> types   // types of col	
    ) {

        // BASECASE
        if (phi.isEmpty()) {
            if (n == 0) {
                // we don't exhaust the empty pattern
                return Optional.of(List.of());
            }
            final List<TRSTerm> varList = new LinkedList<>();
            for (int i = 0; i < n; i++) {
                varList.add(TRSTerm.createVariable("_"));
            }

            return Optional.of(varList);
        } else if (n == 0) {
            // pattern matrix is not empty but every pattern is matched, so every pattern is exhausted
            return Optional.empty();
        }

        // Construct Sigma: set of constructors that appear as root in the first col of Phi
        final Set<FunctionSymbol> sigma = new HashSet<>();
        for (final var p : phi) {
            final TRSTerm p_i0 = p.get(0);
            if (p_i0 instanceof TRSFunctionApplication) {
                final FunctionSymbol root = ((TRSFunctionApplication) p_i0).getRootSymbol();
                sigma.add(root);
            }
        }

        // Case 1: Sigma is a complete type (all symbols of type are included in sigma)
        if (types.get(0).equals(sigma)) {
            for (final var c_k : sigma) {
                final var sMatrix = specialise_matrix(c_k, phi);
                final var head_type = types.get(0);
                // append head type to spec_types
                final List<Set<FunctionSymbol>> spec_types = new LinkedList<>();
                for (int i = 0; i < c_k.getArity(); i++) {
                    spec_types.add(head_type);
                }
                types.stream()
                    .skip(1)
                    .forEach(spec_types::add);

                final var ret = check(sMatrix, c_k.getArity() + n - 1, spec_types);
                if (ret.isPresent()) {
                    // found non matched patter: r_1 ... r_ak p_2 ... p_N
                    // return pattern c_k(r_1 ... r_ak) p_2 ... p_N
                    final List<TRSTerm> copy = new ArrayList<>(ret.get());
                    final List<TRSTerm> args = copy.subList(0, copy.size() - n + 1);
                    final List<TRSTerm> xs = copy.subList(copy.size() - n + 1, copy.size());

                    final List<TRSTerm> x = new ArrayList<>();
                    x.add(TRSTerm.createFunctionApplication(c_k, args));
                    xs.forEach(x::add);
                    return Optional.of(x);
                }
            }
            // all recursive calls returned \bot, so we return \bot
            return Optional.empty();
            // Case 2: Sigma is not complete
            // Just one recursive call
        } else {
            final var dMatrix = default_matrix(phi);
            //default types
            final List<Set<FunctionSymbol>> def_types = new LinkedList<>();
            types.stream()
                .skip(1)
                .forEach(def_types::add);
            final var ret = check(dMatrix, n - 1, def_types);
            if (ret.isPresent()) {
                // recursive call found pattern p_2 ... p_N
                if (sigma.isEmpty()) {
                    // return _ p_2 ... p_N
                    final List<TRSTerm> xs = new ArrayList<>(ret.get());
                    final List<TRSTerm> x = new ArrayList<>();
                    x.add(TRSTerm.createVariable("x"));
                    xs.forEach(x::add);
                    return Optional.of(x);
                } else {
                    // return c(_ ... _) p_2 ... p_N where c \in type \setminus sigma
                    for (final var c : types.get(0)) {
                        if (!sigma.contains(c)) {
                            final var gen = new FreshVarGenerator();
                            final var var = TRSTerm.createVariable("x");
                            final List<TRSTerm> vargs = new LinkedList<>();
                            for (int i = 0; i < c.getArity(); i++) {
                                vargs.add(gen.getFreshVariable(var, false));
                            }

                            final List<TRSTerm> xs = new ArrayList<>(ret.get());
                            final List<TRSTerm> x = new ArrayList<>();
                            x.add(TRSTerm.createFunctionApplication(c, ImmutableCreator.create(vargs)));
                            xs.forEach(x::add);
                            return Optional.of(x);
                        }
                    }
                }
            } else {
                return Optional.empty();
            }
        }
        assert false : "reached apparently not so unreachable, unreachable state :(";
        return Optional.empty();
    }

    public List<ImmutableList<TRSTerm>> default_matrix(final List<ImmutableList<TRSTerm>> phi) {
        final List<ImmutableList<TRSTerm>> out = new LinkedList<>();
        for (final var row : phi) {
            final var p_0i = row.get(0);
            // case 1: p_0i is variable -> return p_1i ... p_ni
            if (p_0i.isVariable()) {
                final List<TRSTerm> new_row = new LinkedList<>();
                if (row.size() > 1) {
                    row.stream()
                        .skip(1)
                        .forEach(new_row::add);
                }
                out.add(ImmutableCreator.create(new_row));
            }

            // case 2: root p_0i is constructor -> no row (do nothing)
        }
        return out;
    }

    public List<ImmutableList<TRSTerm>> specialise_matrix(final FunctionSymbol c, final List<ImmutableList<TRSTerm>> phi) {
        final List<ImmutableList<TRSTerm>> out = new LinkedList<>();
        final var gen = new FreshVarGenerator();
        for (final var row : phi) {
            final var p_0i = row.get(0);
            // case 0: p_0i is variable
            if (p_0i.isVariable()) {
                final List<TRSTerm> new_row = IntStream.range(0, c.getArity())
                    .mapToObj(x -> gen.getFreshVariable((TRSVariable) p_0i, false))
                    .collect(Collectors.toList());

                row.stream()
                    .skip(1)
                    .forEach(new_row::add);
                out.add(ImmutableCreator.create(new_row));
            } else if (((TRSFunctionApplication) p_0i).getRootSymbol().equals(c)) {
                // case 1: root of p_0i is c -> append row by arguments of p_0i
                final List<TRSTerm> new_row = new LinkedList<>();
                final ImmutableList<TRSTerm> arguments = ((TRSFunctionApplication) p_0i).getArguments();

                arguments.stream().forEach(new_row::add);
                row.stream()
                    .skip(1)
                    .forEach(new_row::add);
                out.add(ImmutableCreator.create(new_row));
            }
            // case 2: root of p_0i is not c -> no row (do nothing)
        }
        return out;
    }

    public boolean isExhaustive() {
        // only guarantee expected behavior for left linear constructor based trs
        assert (isLeftLinear() && isConstructorBased()) : "can only check exhaustion on left-linear and constructor based PTRS";

        // construct pattern-matrix phi for each function symbol
        final Map<FunctionSymbol, List<ImmutableList<TRSTerm>>> phi = new HashMap<>();

        final ImmutableSet<Rule> rulesNonProb = getNonProbAbstraction().getR();
        final Set<Rule> copy = new HashSet<>();
        rulesNonProb.forEach(copy::add);
        final var typeEnv = TypeInference.inferEnv(rulesNonProb, getSignature(), getDefSymbolsOfR());

        // we require every sort to have at least on constant
        for (final var s : typeEnv.sorts().keySet()) {
            boolean constantIsPresent = false;
            for (final var ctor : typeEnv.sorts().get(s).constructors()) {
                // found a constant
                if (ctor.getArity() == 0) {
                    constantIsPresent = true;
                }
            }
            if (!constantIsPresent) {
                System.out.println("Exhaustion check failed: Type: " + s + " : " + typeEnv.sorts().get(s).constructors() + " does not contain a constant.");
                return false;
            }
        }

        for (final var r : getPR()) {
            final TRSFunctionApplication lhs = r.getLeft();
            final FunctionSymbol root = lhs.getFunctionSymbol();
            if (getDefSymbolsOfR().contains(root)) {
                phi.computeIfAbsent(root, key -> new LinkedList<>())
                    .add(lhs.getArguments());
            }
        }

        // Check if each def symbol is exhaustive
        for (final var f : this.defSymbolsOfR) {
            final DefSig sig = typeEnv.defs().get(f);
            final List<Set<FunctionSymbol>> types = new LinkedList<>();
            for (final var argC : sig.argClasses()) {
                types.add(typeEnv.sorts().get(argC).constructors());
            }

            final var unexhaustedPatterns = check(phi.get(f), f.getArity(), types);

            if (unexhaustedPatterns.isPresent()) {
                System.out.println(f + " does not exhaust " + unexhaustedPatterns.get());
                return false;
            }
        }

        return true;
    }
}
