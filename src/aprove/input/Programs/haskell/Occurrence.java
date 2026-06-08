package aprove.input.Programs.haskell;

/**
 * Occurrence is a
 * <a href="https://en.wikipedia.org/wiki/Complete_lattice">complete lattice</a>
 * with least element 'MIXED' and greatest element 'UNUSED'.
 */
public enum Occurrence {
    MIXED, // + and -
    JUST_NEG,
    JUST_POS,
    STRICT_POS,
//    GUARD_POS, //not quite sure (think it is for records)
    UNUSED; // does not occur

    /**
     * Simulates behavior of additive of the Occurrence semiring (a+b):
     * 'UNUSED' is neutral (zero) and 'MIXED' is dominant
     *
     * @param other the other Occurrence (b) added to 'this' (a)
     * @return 'this + other'
     */
    public Occurrence oplus(Occurrence other) {

        if (this == MIXED || other == MIXED) return MIXED;          // dominant

        if (this == UNUSED) return other;
        if (other == UNUSED) return this;

        if (this == JUST_NEG && other == JUST_NEG) return JUST_NEG;
        if (this == JUST_NEG || other == JUST_NEG) return MIXED;

//        if (this == GUARD_POS) return other;
//        if (other == GUARD_POS) return this;

        if (this == STRICT_POS) return other;
        if (other == STRICT_POS) return this;

        return JUST_POS;                                                // both JUST_POS
    }

    /**
     * Simulates behavior of multiplicative of the Occurrence semiring (a*b):
     * 'STRICT_POS' is neutral (one) and 'UNUSED' dominant
     *
     * @param other the other Occurrence (b) 'this' (a) is to be multiplied by
     * @return 'this * other'
     */
    public Occurrence otimes(Occurrence other) {
        if (this == UNUSED || other == UNUSED) return UNUSED;
        if (this == MIXED || other == MIXED) return MIXED;
        if (this == JUST_NEG && other == JUST_NEG) return JUST_POS;
        if (this == JUST_NEG || other == JUST_NEG) return JUST_NEG;
        if (this == JUST_POS || other == JUST_POS) return JUST_POS;
//        if (this == GUARD_POS || other == GUARD_POS) return GUARD_POS;
        return STRICT_POS;
    }

    /**
     * @return true => mixed, just negative or just positive,<p> false => strict positive, guarded positive or unused
     */
    public boolean isNotStrictlyPositive() {
        return this == MIXED || this == JUST_NEG || this == JUST_POS;
    }


    public String toPrettyString() {
        return switch (this) {
            case MIXED -> "*";
            case JUST_NEG -> "~";
            case JUST_POS -> "+";
            case STRICT_POS -> "++";
//            case GUARD_POS -> "g+";
            case UNUSED -> "_";
        };
    }
}
