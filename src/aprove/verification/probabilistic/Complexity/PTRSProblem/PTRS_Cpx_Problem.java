package aprove.verification.probabilistic.Complexity.PTRSProblem;

import java.util.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
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
public class PTRS_Cpx_Problem extends DefaultBasicObligation implements Immutable {

    // ================================================================================
    // Properties
    // ================================================================================

    private final RewriteStrategy strat;
    private final boolean basic;

    private final Set<ProbabilisticRule> PR;

    /* Computed Values */
    private volatile CriticalPairs critPairs;
    private final ImmutableSet<FunctionSymbol> signature;
    private volatile ImmutableSet<FunctionSymbol> defSymbolsOfR;
    private volatile ImmutableMap<FunctionSymbol, ImmutableSet<ProbabilisticRule>> ruleMap;

    private final int hashCode;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    public PTRS_Cpx_Problem(final Set<ProbabilisticRule> probabilisticRules,
        final RewriteStrategy strat,
        final ProbabilisticTerminationResult target,
        final boolean basic) {
        super("CpxPTRS", "Complexity Probabilistic TRS");

        this.PR = probabilisticRules;
        this.strat = strat;
        this.basic = basic;
        this.critPairs = null;
        this.defSymbolsOfR = null;
        this.ruleMap = null;
        final Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.PR);
        this.signature = ImmutableCreator.create(signature);
        this.hashCode = Objects.hash(this.PR);

        calculateDefSymbolsAndRuleMap();
    }

    public PTRS_Cpx_Problem(final ImmutableSet<ProbabilisticRule> probabilisticRules,
        final RewriteStrategy strat,
        final boolean basic) {
        super("CpxPTRS", "Complexity Probabilistic TRS");

        this.PR = probabilisticRules;
        this.strat = strat;
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
    public static PTRS_Cpx_Problem create(final ImmutableSet<ProbabilisticRule> PR,
        final RewriteStrategy strat,
        final boolean basic) {
        return new PTRS_Cpx_Problem(PR, strat, basic);
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

    public ImmutableSet<FunctionSymbol> getSignature() {
        return this.signature;
    }

    public ImmutableSet<FunctionSymbol> getDefSymbolsOfR() {
        return this.defSymbolsOfR;
    }

    public ImmutableSet<FunctionSymbol> getConstSymbolsOfR() {
        final Set<FunctionSymbol> constSig = new HashSet<>(this.signature);
        constSig.removeAll(this.defSymbolsOfR);
        return ImmutableCreator.create(constSig);
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

    public boolean isNonErasing() {
        for (final ProbabilisticRule rule : getPR()) {
            for (final Rule r : rule.getNonProbabilisticRepresentation()) {
                if (!r.isNonErasing()) {
                    return false;
                }
            }
        }
        return true;
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
        if (this.basic) {
            return switch (this.strat) {
                case FULL -> "cpx_ptrs_b";
                case INNERMOST -> "cpx_ptrs_i_b";
                case OUTERMOST -> "cpx_ptrs_o_b";
                case PARALLEL_SIMULTANEOUS -> "cpx_ptrs_ps_b";
                case PARALLEL_SIMULTANEOUS_INNERMOST -> "cpx_ptrs_psi_b";
                case PARALLEL_SIMULTANEOUS_OUTERMOST -> "cpx_ptrs_pso_b";
                default -> "cpx_ptrs_b";
            };
        } else {
            return switch (this.strat) {
                case FULL -> "cpx_ptrs";
                case INNERMOST -> "cpx_ptrs_i";
                case OUTERMOST -> "cpx_ptrs_o";
                case PARALLEL_SIMULTANEOUS -> "cpx_ptrs_ps";
                case PARALLEL_SIMULTANEOUS_INNERMOST -> "cpx_ptrs_psi";
                case PARALLEL_SIMULTANEOUS_OUTERMOST -> "cpx_ptrs_pso";
                default -> "cpx_ptrs";
            };
        }
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Complexity");
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
        final PTRS_Cpx_Problem that = (PTRS_Cpx_Problem) o;
        return this.hashCode == that.hashCode &&
            Objects.equals(this.PR, that.PR);
    }
}
