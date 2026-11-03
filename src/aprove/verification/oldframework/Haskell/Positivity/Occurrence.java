package aprove.verification.oldframework.Haskell.Positivity;

/**
 * Polarity of an occurrence of a type in another type, as used for checking strict positivity.
 *
 * The values form a lattice with least element {@link #MIXED} and greatest element {@link #UNUSED}:
 * <pre>
 *            UNUSED
 *            /    \
 *     STRICT_POS   \
 *         |      JUST_NEG
 *      JUST_POS    /
 *            \    /
 *            MIXED
 * </pre>
 * Together with {@link #oplus(Occurrence)} (as the meet, used to join parallel paths) and {@link #otimes(Occurrence)}
 * (composition along a path), they form a semiring with zero {@link #UNUSED} and one {@link #STRICT_POS}.
 */
public enum Occurrence {
    /** The type occurs both positively and negatively. */
    MIXED,
    /** The type occurs only negatively, i.e., to the left of an odd number of arrows. */
    JUST_NEG,
    /** The type occurs only positively, but at least once to the left of an arrow. */
    JUST_POS,
    /** The type occurs only strictly positively, i.e., never to the left of an arrow. */
    STRICT_POS,
    /** The type does not occur. */
    UNUSED;

    /**
     * Combines the polarities of two alternative paths, i.e., the addition of the semiring.
     * This is used to combine individual branches in Sum types or individual fields of a constructor.
     * {@link #UNUSED} is neutral and {@link #MIXED} is absorbing.
     *
     * @param other the polarity to add to this polarity
     * @return {@code this + other}
     */
    public Occurrence oplus(final Occurrence other) {
        if (this == MIXED || other == MIXED) {
            return MIXED;
        }
        if (this == UNUSED) {
            return other;
        }
        if (other == UNUSED) {
            return this;
        }
        if (this == JUST_NEG && other == JUST_NEG) {
            return JUST_NEG;
        }
        if (this == JUST_NEG || other == JUST_NEG) {
            return MIXED;
        }
        if (this == STRICT_POS) {
            return other;
        }
        if (other == STRICT_POS) {
            return this;
        }
        // both JUST_POS
        return JUST_POS;
    }

    /**
     * Composes the polarities of two consecutive path segments, i.e., the multiplication of the semiring.
     * {@link #STRICT_POS} is neutral and {@link #UNUSED} is absorbing.
     * This is used when a field in a data declaration refers to another data type or for nested types.
     *
     * @param other the polarity to multiply this polarity with
     * @return {@code this * other}
     */
    public Occurrence otimes(final Occurrence other) {
        if (this == UNUSED || other == UNUSED) {
            return UNUSED;
        }
        if (this == MIXED || other == MIXED) {
            return MIXED;
        }
        if (this == JUST_NEG && other == JUST_NEG) {
            return JUST_POS;
        }
        if (this == JUST_NEG || other == JUST_NEG) {
            return JUST_NEG;
        }
        if (this == JUST_POS || other == JUST_POS) {
            return JUST_POS;
        }
        return STRICT_POS;
    }

    /**
     * @return {@code true} iff this polarity is {@link #MIXED}, {@link #JUST_NEG} or {@link #JUST_POS}
     */
    public boolean isNotStrictlyPositive() {
        return this == MIXED || this == JUST_NEG || this == JUST_POS;
    }

    /**
     * @return a short symbolic representation of this polarity
     */
    public String toPrettyString() {
        return switch (this) {
            // escaped, since the sources are compiled as ISO-8859-1
            case MIXED -> "\u00B1";
            case JUST_NEG -> "-";
            case JUST_POS -> "+";
            case STRICT_POS -> "++";
            case UNUSED -> "0";
        };
    }
}
