package aprove.verification.probabilistic.BasicStructures;

import java.util.*;
import java.util.Map.*;
import java.util.stream.*;

import org.apache.commons.math3.fraction.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * A probabilistic rule is a rewriting rule with probabilistic choice on the right hand side.
 * I.e. a rule that maps a term (which may not be a variable) to a multi-distribution over terms.
 * We have the standard rule restrictions, namely that the lhs is not a variable and that the
 * variables of the rhs is a subset of the variables on the lhs (i.e., V(r) subset V(l)).
 *
 * @author Jan-Christoph Kassing
 */
public final class ProbabilisticRule extends GeneralizedProbabilisticRule
    implements
    Immutable {

    // ================================================================================
    // Properties
    // ================================================================================

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    /**
     * creates a new rule.
     * Restrictions: stdL is null iff stdR is null
     *   if stdL is given, then stdL -> stdR is the
     *   standard representation of l -> r
     * @param l - a non-variable term
     * @param r - a term with less variables then l
     * @param stdL - null or the lhs of the standard representation of l->r
     * @param stdR - null or the rhs of the standard representation of l->r
     */
    private ProbabilisticRule(final TRSFunctionApplication l,
        final MultiDistribution<TRSTerm> r,
        final TRSFunctionApplication stdL,
        final MultiDistribution<TRSTerm> stdR) {
        super(l, r, stdL, stdR);
        if (Globals.useAssertions) {
            final boolean ruleProper = ProbabilisticRule.checkProperLandR(l, r);
            assert (ruleProper);
        }
    }

    /**
     * create a new probabilistic rule
     * @param l the left hand side
     * @param r the right hand side. must be a distribution (not subdistribution).
     * @return the new instance
     */
    public static ProbabilisticRule create(final TRSFunctionApplication l, final MultiDistribution<TRSTerm> r) {
        return new ProbabilisticRule(l, r, null, null);
    }

    /**
     * create a new probabilistic rule with, where the rhs contains only a single element with probability 1.
     * @param l the left hand side
     * @param r the right hand side. must be a distribution (not subdistribution).
     * @return the new instance
     */
    public static ProbabilisticRule create(final TRSFunctionApplication l, final TRSTerm r) {
        final HashMultiSet<Pair<TRSTerm, BigFraction>> probabilityMapping = new HashMultiSet<>();

        final Pair<TRSTerm, BigFraction> pair = new Pair<>(r, BigFraction.ONE);
        probabilityMapping.add(pair);
        final MultiDistribution<TRSTerm> rMult = new MultiDistribution<>(probabilityMapping);

        return new ProbabilisticRule(l, rMult, null, null);
    }

    /**
     * create a new probabilistic rule. Only use this variant if you know what you are doing.
     *
     * @see ProbabilisticRule#create(TRSFunctionApplication, MultiDistribution)
     */
    public static ProbabilisticRule create(final TRSFunctionApplication l,
        final MultiDistribution<TRSTerm> r,
        final TRSFunctionApplication stdL,
        final MultiDistribution<TRSTerm> stdR) {
        return new ProbabilisticRule(l, r, stdL, stdR);
    }

    // ================================================================================
    // Accessors
    // ================================================================================

    /**
     * Get a set of rules that simulate the behavior of this probabilistic rule by replacing probabilistic choice
     * with non-determinism, i.e. the set {l -> t | t in supp(r)}
     * If this rule is deterministic, a singleton set is returned and the returned rule is equivalent to this rule.
     * @see ProbabilisticRule#isDeterministic()
     * @return a set of rules
     */
    @Override
    public Set<? extends Rule> getNonProbabilisticRepresentation() {
        final Set<Rule> res = new LinkedHashSet<>();

        for (final TRSTerm t : this.r.getSupport()) {
            res.add(Rule.create(this.l, t));
        }

        return res;
    }

    /**
     * checks whether t is a basic term w.r.t. the given rules, i.e., the root of t is a defined symbol and all
     * arguments of t are constructor terms.
     * @param t
     * @param rules
     */
    public static boolean isBasicTerm(final TRSTerm t, final Iterable<? extends ProbabilisticRule> rules) {
        if (t.isVariable()) {
            return false;
        }
        final Set<FunctionSymbol> defined = new HashSet<>();
        for (final ProbabilisticRule rule : rules) {
            defined.add(rule.getLeft().getRootSymbol());
        }
        final TRSFunctionApplication ft = (TRSFunctionApplication) t;
        if (!defined.contains(ft.getRootSymbol())) {
            return false;
        }
        for (final TRSTerm arg : ft.getArguments()) {
            for (final FunctionSymbol g : arg.getFunctionSymbols()) {
                if (defined.contains(g)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * checks whether some basic term reaches an instance of t (in a context) with positive probability in at most
     * one step, i.e., t is basic or some rule with a basic left-hand side has a term in the support of its
     * right-hand side that contains an instance of t. For full rewriting, non-AST (non-SAST) of t then implies
     * non-AST (non-SAST) of this basic term.
     * @param t
     * @param rules
     */
    public static boolean isReachedFromBasicTerm(final TRSTerm t, final Collection<? extends ProbabilisticRule> rules) {
        if (ProbabilisticRule.isBasicTerm(t, rules)) {
            return true;
        }
        for (final ProbabilisticRule rule : rules) {
            if (ProbabilisticRule.isBasicTerm(rule.getLeft(), rules)) {
                for (final TRSTerm r : rule.getRight().getSupport()) {
                    if (NonTerminationProbProofNode.containsInstanceOf(r, t)) {
                        return true;
                    }
                }
            }
        }
        return false;
    }

    /**
     * returns a map from defined symbols (of rhss) to corresponding reversed non-probabilistic rules. Collapsing rules
     * have null as "defined symbol".
     * @param rules
     */
    public static Map<FunctionSymbol, Set<Rule>> getReversedRuleMap(final Iterable<? extends ProbabilisticRule> rules) {
        final Map<FunctionSymbol, Set<Rule>> reverseRuleMap = new LinkedHashMap<>();
        for (final ProbabilisticRule rule : rules) {
            for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
                final TRSTerm rhs = entry.getKey().getKey();
                final FunctionSymbol f = rhs.isVariable() ? null : ((TRSFunctionApplication) rhs).getRootSymbol();

                Set<Rule> fRules = reverseRuleMap.get(f);
                if (fRules == null) {
                    fRules = new LinkedHashSet<>();
                    reverseRuleMap.put(f, fRules);
                }
                fRules.add(Rule.create(rule.getLeft(), rhs));
            }
        }

        return reverseRuleMap;
    }

    @Override
    public ProbabilisticRule getStandardRepresentation() {
        return ProbabilisticRule.create(getLhsInStandardRepresentation(), getRhsInStandardRepresentation());
    }

    private static boolean checkProperLandR(final TRSFunctionApplication l, final MultiDistribution<TRSTerm> r) {
        return l != null
            && r != null
            && r.isDistribution()
            && l.getVariables()
                .containsAll(
                    r.getSupport()
                        .stream()
                        .flatMap(t -> t.getVariables().stream())
                        .collect(Collectors.toSet()));
    }

    // ================================================================================
    // canonicalization
    // ================================================================================

    /**
     * renames the variables with given prefix and
     * numbers starting from STANDARD_NUMBER.
     * E.g., for rule = f(x,y,x1,y) -> f(y,x,x,a)
     *           prefix = x
     *           STANDARD_NUMBER = 0
     *    we obtain  f(x0,x1,x2,x1) -> f(x1,x0,x0,a).
     *
     * The standard representation of a rule is
     * rule.getWithRenumberedVariables(STANDARD_PREFIX);
     * @param prefix
     * @return
     */
    @Override
    public ProbabilisticRule getWithRenumberedVariables(final String prefix) {
        final Map<TRSVariable, TRSVariable> map = new HashMap<>();
        final ImmutablePair<? extends TRSFunctionApplication, Integer> stdLAndInt = this.l.renumberVariables(map,
            prefix,
            TRSTerm.STANDARD_NUMBER);
        final HashMultiSet<Pair<TRSTerm, BigFraction>> stdProbabilityMap = new HashMultiSet<>();
        Integer nextFreeNr = stdLAndInt.y;
        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : this.r.getProbabilityMapping().entrySet()) {
            final TRSTerm term = entry.getKey().getKey();
            final BigFraction prob = entry.getKey().getValue();
            final Integer amount = entry.getValue();
            final ImmutablePair<? extends TRSTerm, Integer> stdEAndInt = term.renumberVariables(map, prefix, nextFreeNr);
            stdProbabilityMap.put(new Pair<>(stdEAndInt.x, prob), amount);
            nextFreeNr = stdEAndInt.y;
        }
        return new ProbabilisticRule(stdLAndInt.x,
            new MultiDistribution<>(stdProbabilityMap).getCanonicalRepresentation(),
            this.stdL,
            this.stdR);
    }

    // ================================================================================
    // Utility
    // ================================================================================

    /**
     * Two probabilistic rules are considered equal if their canonicalized left hand side and right hand sides are equal.
     */
    @Override
    public boolean equals(final Object other) {
        if (this == other) {
            return true;
        }
        if (other instanceof final ProbabilisticRule rule) {
            return this.hashCode == rule.hashCode && this.stdL.equals(rule.stdL) && this.stdR.equals(rule.stdR);
        }
        return false;
    }

    // ================================================================================
    // Annotated Terms
    // ================================================================================

    /**
     * returns the number of annotations in all the rhs of this rule.
     * @param deAnnoMap - Maps annotated function symbols to its original ones
     * @return number of annotations in the rhs
     */
    public int countAnnos(final Map<FunctionSymbol, FunctionSymbol> deAnnoMap) {
        int sum = 0;
        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : this.r.getProbabilityMapping().entrySet()) {
            final TRSTerm term = entry.getKey().getKey();
            final Integer amount = entry.getValue();

            int annoSum = 0;
            final var counts = term.getFunctionSymbolCount();
            for (final FunctionSymbol anno : deAnnoMap.keySet()) {
                annoSum += counts.get(anno);
            }
            sum += annoSum * amount;
        }
        return sum;
    }

    /**
     * returns whether this is an ADP with annotations in the lhs l^# -> {...}
     * @param deAnnoMap - Maps annotated function symbols to its original ones
     * @return true if this is an ADP
     */
    public boolean isADP(final Map<FunctionSymbol, FunctionSymbol> deAnnoMap) {
        return deAnnoMap.keySet().contains(getLeft().getRootSymbol());
    }

    /**
     * returns the flattened version of this ADP
     * @param deAnnoMap - Maps annotated function symbols to its original ones
     * @return flat(l^# -> {...})
     */
    public ProbabilisticRule removeAnnos(final Map<FunctionSymbol, FunctionSymbol> deAnnoMap) {
        final TRSFunctionApplication flatlhs = this.l.renameAtAllMap(this.l.getPositions(), deAnnoMap);
        final HashMultiSet<Pair<TRSTerm, BigFraction>> stdProbabilityMap = new HashMultiSet<>();
        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : this.r.getProbabilityMapping().entrySet()) {
            final TRSTerm term = entry.getKey().getKey();
            final BigFraction prob = entry.getKey().getValue();
            final Integer amount = entry.getValue();
            final TRSTerm flatrhs = term.renameAtAllMap(term.getPositions(), deAnnoMap);

            final Pair<TRSTerm, BigFraction> newPair = new Pair<>(flatrhs, prob);
            if (stdProbabilityMap.contains(newPair)) {
                final Integer amountAlreadyContained = stdProbabilityMap.get(newPair);
                stdProbabilityMap.put(new Pair<>(flatrhs, prob), amountAlreadyContained + amount);
            } else {
                stdProbabilityMap.put(new Pair<>(flatrhs, prob), amount);
            }
        }
        return ProbabilisticRule.create(flatlhs, new MultiDistribution<>(stdProbabilityMap).getCanonicalRepresentation());
    }

    /**
     * returns the set of all annotated subterms in the rhs of this rule
     * @param deAnnoMap - Maps annotated function symbols to its original ones
     * @return {#_varepsilon(t) | t annotated subterm of some r in the rhs}
     */
    public Set<TRSFunctionApplication> getAllAnnoSubterms(final Map<FunctionSymbol, FunctionSymbol> deAnnoMap) {
        final Set<TRSFunctionApplication> res = new HashSet<>();
        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : this.r.getProbabilityMapping().entrySet()) {
            final TRSTerm term = entry.getKey().getKey();
            res.addAll(term.getAnnoSubterms(deAnnoMap));
        }
        return res;
    }
}
