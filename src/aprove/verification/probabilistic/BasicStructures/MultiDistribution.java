package aprove.verification.probabilistic.BasicStructures;

import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Represents a (Multi-)Distribution.
 * There is actually no guarantee that an instance of this class is a distribution. To have this
 * guarantee, create it via the factory method.
 *
 * @param <T> The Domain of the distribution.
 *
 * @author Jan-Christoph Kassing, davidkor
 * @version $Id$
 */
public class MultiDistribution<T> implements
    Immutable,
    Exportable {

    // ================================================================================
    // Properties
    // ================================================================================

    protected final HashMultiSet<Pair<T, BigFraction>> probabilityMap;

    /* computed values */
    protected final Map<T, BigFraction> supportToProbability;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    /**
     * Create a distribution with the provided mapping.
     * There is no guarantee that the resulting instance is a valid distribution.
     *
     * @see SubDistribution#create(Map)
     * @see SubDistribution#isSubDistribution()
     *
     * @param elementsToProbabilities The mapping of objects to probabilities.
     */
    public MultiDistribution(final HashMultiSet<Pair<T, BigFraction>> elementsToProbabilities) {
        this.probabilityMap = new HashMultiSet<>(elementsToProbabilities);
        this.supportToProbability = new HashMap<>();
        for (final Entry<Pair<T, BigFraction>, Integer> entry : this.probabilityMap.entrySet()) {
            final T elem = entry.getKey().getKey();
            final BigFraction prob = entry.getKey().getValue();
            final Integer amount = entry.getValue();
            if (prob.compareTo(BigFraction.ZERO) > 0) {
                this.supportToProbability.merge(elem, prob.multiply(amount), BigFraction::add);
            }
        }
    }

    /**
     * Create a new distribution from the provided mapping and check that it results in a valid (multi-)distribution.
     * @param elementsToProbabilities A mapping of objects to probabilities
     * @param <T> the domain of the resulting distribution
     * @return a valid (sub)distribution from the provided mapping
     * @throws InvalidProbabilitiesException thrown if a probability is not between 0 and 1
     * @throws ProbabilityOutOfRangeException thrown if the probabilities don't sum up to a value between 0 and 1
     */
    public static <T> MultiDistribution<T> create(final HashMultiSet<Pair<T, BigFraction>> elementsToProbabilities)
        throws InvalidProbabilitiesException {

        // Check whether the probability mass sums to 1
        BigFraction totalProbabilityMass = BigFraction.ZERO;
        for (final Entry<Pair<T, BigFraction>, Integer> entry : elementsToProbabilities.entrySet()) {
            final BigFraction prob = entry.getKey().getValue();
            final Integer amount = entry.getValue();
            if (prob.compareTo(BigFraction.ZERO) < 0 || prob.compareTo(BigFraction.ONE) > 0) {
                throw new InvalidProbabilitiesException(prob);
            }
            totalProbabilityMass = totalProbabilityMass.add(prob.multiply(amount));
        }
        if (totalProbabilityMass.compareTo(BigFraction.ONE) != 0) { // No it does not sum to 1
            throw new InvalidTotalProbabilityException(totalProbabilityMass);
        }

        return (new MultiDistribution<>(elementsToProbabilities)).getCanonicalRepresentation();
    }

    // ================================================================================
    // Accessors
    // ================================================================================

    /**
     * Get the support, i.e. everything that has non-zero probability.
     *
     * @see SubDistribution#getSupporRestrictedMapping()
     * @return A set representing the support of the distribution.
     */
    public Set<T> getSupport() {
        return this.supportToProbability.keySet();
    }

    /**
     * Get the mapping restricted to the support and add up all probabilites for elements
     * that occur multiple times as a key inside of our multi-distribution.
     *
     * @see SubDistribution#getSupport()
     * @see SubDistribution#getCanonicalRepresentation()
     * @return A mapping of the support to probabilities.
     */
    public Map<T, BigFraction> getSupportMapping() {
        return this.supportToProbability;
    }

    /**
     * Get the complete probability (multi-)mapping.
     *
     * @return A probability (multi-)mapping.
     */
    public HashMultiSet<Pair<T, BigFraction>> getProbabilityMapping() {
        return this.probabilityMap;
    }

    /**
     * Gets the canonical representation of this distribution. I.e. an optimized version of the object with
     * no elements mapped to zero.
     *
     * @return an optimized representation of this distribution
     */
    public MultiDistribution<T> getCanonicalRepresentation() {
        final HashMultiSet<Pair<T, BigFraction>> canonincalprobabilityMap = new HashMultiSet<>();
        for (final Entry<Pair<T, BigFraction>, Integer> entry : this.probabilityMap.entrySet()) {
            final BigFraction prob = entry.getKey().getValue();
            final Integer amount = entry.getValue();
            if (prob.compareTo(BigFraction.ZERO) > 0) {
                canonincalprobabilityMap.add(entry.getKey(), amount);
            }
        }
        return new MultiDistribution<>(canonincalprobabilityMap);
    }

    /**
     * Get the whole probability mass of this distribution.
     *
     * @return sum of all probabilities
     */
    public BigFraction getProbabilitySum() {
        return this.supportToProbability.values().stream().reduce(BigFraction.ZERO, BigFraction::add);
    }

    /**
     * get the probability of a single element.
     * @param element the element we want to get the probability of.
     * @return the probability of element.
     */
    public BigFraction p(final T element) {
        return this.supportToProbability.getOrDefault(element, BigFraction.ZERO);
    }

    /**
     * Returns true, if all probabilites sum up to 1.
     * @return true if this is a distribution
     */
    public boolean isDistribution() {
        return this.getProbabilitySum().equals(BigFraction.ONE);
    }

    /**
     * Checks if this always chooses a single item with probability 1.
     * @return true, if this distribution is deterministic.
     */
    public boolean isDeterministic() {
        return this.supportToProbability.size() == 1 && this.isDistribution();
    }

    // ================================================================================
    // Utility
    // ================================================================================

    /**
     * Two distributions are equal, if they map all objects to the same probability value.
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj instanceof final MultiDistribution<?> other) {
            return this.getProbabilityMapping().equals(other.getProbabilityMapping());
        }
        return false;
    }

    /**
     * Two distributions have the same hash code, if they map all objects to the same probability value.
     */
    @Override
    public int hashCode() {
        return this.getProbabilityMapping().hashCode();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String export(final Export_Util eu) {
        final StringBuilder sb = new StringBuilder();

        int remConds = this.probabilityMap.size();
        for (final Entry<Pair<T, BigFraction>, Integer> entry : this.probabilityMap.entrySet()) {
            final T elem = entry.getKey().getKey();
            final BigFraction prob = entry.getKey().getValue();
            final Integer amount = entry.getValue();
            for (int i = 0; i < amount; i++) {
                sb.append(prob).append(' ').append(eu.colon()).append(' ');
                if (elem instanceof Exportable) {
                    sb.append(((Exportable) elem).export(eu));
                } else {
                    sb.append(elem.toString());
                }
                remConds--;
                if (remConds > 0) {
                    sb.append(' ').append(eu.probabilistiChoiceOperator()).append(' ');
                }
                if (i != amount - 1) {
                    sb.append(' ').append("||").append(' ');
                }
            }
        }

        return sb.toString();
    }

    public static final class Builder<T> {

        private final HashMultiSet<Pair<T, Integer>> inputMapInt;
        private final HashMultiSet<Pair<T, BigFraction>> inputMapFrac;
        private final HashMultiSet<Pair<T, BigFraction>> probabilityMap;

        public Builder() {
            this.inputMapInt = new HashMultiSet<>();
            this.inputMapFrac = new HashMultiSet<>();
            this.probabilityMap = new HashMultiSet<>();
        }

        public void add(final T element, final Integer p) {
            if (p != 0) {
                this.inputMapInt.add(new Pair<>(element, p));
            }
        }

        public void add(final T element, final BigFraction p) {
            if (p.compareTo(BigFraction.ZERO) != 0) {
                this.inputMapFrac.add(new Pair<>(element, p));
            }
        }

        public MultiDistribution<T> build() {
            if (this.inputMapInt.size() > 0 && this.inputMapFrac.size() == 0) {
                int totalSum = 0;
                for (final Entry<Pair<T, Integer>, Integer> entry : this.inputMapInt.entrySet()) {
                    final Integer prob = entry.getKey().getValue();
                    final Integer amount = entry.getValue();
                    totalSum += amount * prob;
                }
                for (final Entry<Pair<T, Integer>, Integer> entry : this.inputMapInt.entrySet()) {
                    final T elem = entry.getKey().getKey();
                    final Integer prob = entry.getKey().getValue();
                    final Integer amount = entry.getValue();
                    for (int i = 0; i < amount; i++) {
                        this.probabilityMap.add(new Pair<>(elem, new BigFraction(prob, totalSum)));
                    }
                }
            } else if (this.inputMapInt.size() == 0 && this.inputMapFrac.size() > 0) {
                BigFraction totalProbability = BigFraction.ZERO;
                for (final Entry<Pair<T, BigFraction>, Integer> entry : this.inputMapFrac.entrySet()) {
                    final T elem = entry.getKey().getKey();
                    final BigFraction prob = entry.getKey().getValue();
                    final Integer amount = entry.getValue();
                    if (prob.compareTo(BigFraction.ZERO) < 0 || prob.compareTo(BigFraction.ONE) > 0) {
                        throw new InvalidProbabilitiesException(prob);
                    }
                    for (int i = 0; i < amount; i++) {
                        totalProbability = totalProbability.add(prob);
                        this.probabilityMap.add(new Pair<>(elem, prob));
                    }
                }
                if (totalProbability.compareTo(BigFraction.ONE) != 0) {
                    throw new InvalidTotalProbabilityException(totalProbability);
                }
            } else {
                throw new BothSyntaxSameRuleException();
            }

            final MultiDistribution<T> product = new MultiDistribution<>(this.probabilityMap);

            return product;
        }
    }

    public static class InvalidTotalProbabilityException extends RuntimeException {

        private static final long serialVersionUID = 3315289172144000320L;

        private InvalidTotalProbabilityException(final BigFraction p) {
            super(p + " is the sum of all probabilities but has to be 1.0");
        }
    }

    public static class InvalidProbabilitiesException extends RuntimeException {

        private static final long serialVersionUID = -399391879721332318L;

        private InvalidProbabilitiesException(final BigFraction p) {
            super(p + " is not a valid probability value. Probabilities must be in the range 0.0 to 1.0");
        }
    }

    public static class BothSyntaxSameRuleException extends RuntimeException {

        private static final long serialVersionUID = -4945449657548159166L;

        private BothSyntaxSameRuleException() {
            super("You are using two different syntax in the same rule.");
        }
    }

    public static class ProbabilityOutOfRangeException extends InvalidProbabilitiesException {

        private static final long serialVersionUID = -698143981357354261L;

        private ProbabilityOutOfRangeException(final BigFraction p) {
            super(p);
        }
    }
}
