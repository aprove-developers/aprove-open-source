/**
 * @author Marc Brockschmidt
 */

package aprove.verification.oldframework.Bytecode.StateRepresentation.AbstractVariables;

import java.math.*;
import java.util.*;

import aprove.verification.oldframework.BasicStructures.Arithmetic.Integer.*;
import aprove.verification.oldframework.Bytecode.Intersector.*;
import aprove.verification.oldframework.Bytecode.Merger.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;

/**
 * Representation of float/double values in our symbolic interpretation,
 * realized by literal values or unknown values.
 */
// TODO For the whole concept of AbstractFloat we need to consider FP-Strictness (FPStrictness).
// See JVMS 3.3.2 and 3.8.
// TODO strictFP is deprecated. Nowadays everything is strict in floating point arithmetic in java 25.
/* The main problem is that values on the operand stack (nowhere) else  may
 * range from an extended exponent set. This opens the question whether
 * termination may depend on this fact. Note that it is not possible to store
 * these extended values in a local variable or a member variable.
 * Which forces us to our own storage system.
 * It is also generally impossible to account for all extended value ranges as
 * the specification places no upper bound on the size and thus there might be
 * infinite many.
 */
public final class AbstractFloat extends AbstractNumber {

    /**
     * Defines whether we know something about this float or not.
     * @author Fabian K&uuml;rten
     */
    private static enum Definedness {
        LITERAL, UKNOWN;
    }

    /**
     * The unknown and non-wide float.
     */
    private static final AbstractFloat UNKNOWN = new AbstractFloat();

    /**
     * Opcode fconst_0 pushes that
     */
    private static final AbstractFloat ZERO = new AbstractFloat(0.0f);

    /**
     * Opcode fconst_1 pushes that
     */
    private static final AbstractFloat ONE = new AbstractFloat(1.0f);

    /**
     * Opcode fconst_2 pushes that
     */
    private static final AbstractFloat TWO = new AbstractFloat(2.0f);

    /**
     * Minus zero is not the same as plus zero.
     */
    private static final AbstractFloat MZERO = new AbstractFloat(-0.0f);

    /**
     * Negative infinity.
     */
    private static final AbstractFloat NEGINF = new AbstractFloat(Float.NEGATIVE_INFINITY);

    /**
     * Positive infinity.
     */
    private static final AbstractFloat POSINF = new AbstractFloat(Float.POSITIVE_INFINITY);

    /**
     * Not a number.
     */
    private static final AbstractFloat NAN = new AbstractFloat(Float.NaN);

    /**
     * How much do we know?
     */
    private final Definedness definedness;

    /**
     * The actual value, don't care if definedNess is not LITERAL
     */
    private final double literal;

    /**
     * Creates a new AbstractFloat representing some unknown float value.
     */
    private AbstractFloat() {
        this.definedness = Definedness.UKNOWN;
        this.literal = Double.NaN; // Does not actually matter
    }

    /**
     * Creates a new {@link AbstractFloat} representing some known literal float value.
     * @param value the literal value
     */
    private AbstractFloat(final double value) {
        this.definedness = Definedness.LITERAL;
        this.literal = value;
    }

    /**
     * @return an unknown float which is wide iff the argument specifies it.
     */
    public static AbstractFloat create() {
        return AbstractFloat.UNKNOWN;
    }

    /**
     * Returns an {@link AbstractFloat} literal value, will reuse the constants.
     * @param value the literal value
     * @return the AbstractFloat
     */
    public static AbstractFloat create(final double value) {
        if (value == AbstractFloat.ONE.literal) {
            return AbstractFloat.ONE;
        } else if (value == AbstractFloat.TWO.literal) {
            return AbstractFloat.TWO;
        } else if (value == 0.0f) {
            // note: -0.0 == +0.0, but 1.0/0.0 != 1.0/0.0
            if (1.0f / value == Double.POSITIVE_INFINITY) {
                return AbstractFloat.ZERO;
            }
            return AbstractFloat.MZERO;
        } else if (Double.isNaN(value)) {
            return AbstractFloat.NAN;
        } else if (Double.isInfinite(value)) {
            if (value < 0.0f) {
                return AbstractFloat.NEGINF;
            }
            return AbstractFloat.POSINF;
        } else {
            return new AbstractFloat(value);
        }
    }

    /**
     * @return The default value defined in the JVMS for this value type
     */
    public static AbstractVariable getDefaultValue() {
        // According to JLS3 4.12.5
        // http://java.sun.com/docs/books/jls/third_edition/html/typesValues.html#4.12.5
        // This has to be 0.0d / 0.0f instead of unknown.
        return AbstractFloat.create(0.0);
    }

    /**
     * Creates a new range from the sum of two existing ranges.
     * @param n value to be added to this
     * @return sum of this instance and the argument
     */
    public AbstractFloat add(final AbstractFloat n) {
        return this.add(n, false);
    }

    /**
     * Creates a new range from the sum of two existing ranges.
     * @param n value to be added to this
     * @param isFPStrict flag indicating if this operation is done in fpstrict conditions.
     * @return sum of this instance and the argument
     */
    public AbstractFloat add(final AbstractFloat n, final boolean isFPStrict) {
        /* JLS: Despite the fact that overflow, underflow, or loss of precision
         * may occur, execution of an fadd instruction never throws a runtime
         * exception.
         */

        final double thisVal = this.literal;
        final double thatVal = n.literal;

        if (this.isLiteral() && n.isLiteral()) {
            /*
             * To handle strictness correctly, try to find out if there might be
             * a different (more exact) result. If that's the case, give out
             * an unknown value. Otherwise, give the (correct) value.
             */
            if (isFPStrict) {
                return AbstractFloat.create(thisVal + thatVal);
            } else {
                final double strictRes = this.addStrict(thisVal, thatVal);
                final double exactRes = this.addExact(thisVal, thatVal);

                if (strictRes == exactRes) {
                    return AbstractFloat.create(strictRes);
                }
            }
        }

        return this.unknown();
    }

    /**
     * @param one some double value.
     * @param two some double value.
     * @return addition result under strictfp conditions.
     */
    private double addStrict(final double one, final double two) {
        return one + two;
    }

    /**
     * @param one some double value.
     * @param two some double value.
     * @return exact addition result, converted to double.
     */
    private double addExact(final Double one, final Double two) {
        if (one.isNaN() || two.isNaN() || one.isInfinite() || two.isInfinite()) {
            return one + two;
        }
        final BigDecimal bOne = BigDecimal.valueOf(one);
        final BigDecimal bTwo = BigDecimal.valueOf(two);
        final BigDecimal res = bOne.add(bTwo);
        return res.doubleValue();
    }

    /**
     * Calculate the cost of losing information from "from" to "to".
     * @param from an abstract float
     * @param to another abstract float
     * @return the associated cost
     */
    private static CostType costForFloat(final AbstractFloat from, final AbstractFloat to) {
        if (from.equals(to)) {
            return CostType.NONE;
        }
        return CostType.FLOAT;
    }

    /**
     * Creates a new range by dividing all values from this by all values from
     * the argument.
     * @param n value to be used as divisor
     * @param sameReference true iff both operands are the very same value.
     * @return the result of the division.
     */
    public AbstractFloat div(final AbstractFloat n, final boolean sameReference) {
        return this.div(n, sameReference, false);
    }

    /**
     * Creates a new range from the division of two existing ranges.
     * @param n value to be added to this
     * @param isFPStrict flag indicating if this operation is done in fpstrict conditions.
     * @return sum of this instance and the argument
     */
    public AbstractFloat div(final AbstractFloat n, final boolean sameReference, final boolean isFPStrict) {

        final double thisVal = this.literal;
        final double thatVal = n.literal;

        if (this.isLiteral() && n.isLiteral()) {
            /*
             * To handle strictness correctly, try to find out if there might be
             * a different (more exact) result. If that's the case, give out
             * an unknown value. Otherwise, give the (correct) value.
             */
            if (isFPStrict) {
                return AbstractFloat.create(thisVal / thatVal);
            } else {
                try {
                    final double strictRes = this.divStrict(thisVal, thatVal);
                    final double exactRes = this.divExact(thisVal, thatVal);

                    if (strictRes == exactRes) {
                        return AbstractFloat.create(strictRes);
                    }
                } catch (ArithmeticException e) {
                    // do nothing
                }
            }
        }

        return this.unknown();
    }

    /**
     * @param one some double value.
     * @param two some double value.
     * @return division result under strictfp conditions.
     */
    private double divStrict(final double one, final double two) {
        return one / two;
    }

    /**
     * @param one some double value.
     * @param two some double value.
     * @return exact division result, converted to double.
     */
    private double divExact(final Double one, final Double two) {
        if (one.isNaN() || two.isNaN() || one.isInfinite() || two.isInfinite()) {
            return one / two;
        }
        final BigDecimal bOne = BigDecimal.valueOf(one);
        final BigDecimal bTwo = BigDecimal.valueOf(two);
        final BigDecimal res = bOne.divide(bTwo);
        return res.doubleValue();
    }

    /**
     * @return true iff this AbstractNumber represents exactly one value.
     */
    @Override
    public boolean isLiteral() {
        return this.definedness.equals(Definedness.LITERAL);
    }

    /**
     * Merge the values represented by this {@link AbstractFloat} with another one.
     * @param otherVar the {@link AbstractFloat} to merge with
     * @return an {@link AbstractNumberMergeResult}, holding an
     * {@link AbstractVariable} that represents all values that are represented
     * by this and otherVar, costs to obtain this merged result and pointers to
     * the original variables.
     */
    public AbstractNumberMergeResult merge(final AbstractNumber otherVar) {
        if (!(otherVar instanceof AbstractFloat)) {
            throw new IllegalArgumentException("Parameter needs to be "
                + "AbstractFloat");
        }
        final AbstractFloat that = (AbstractFloat) otherVar;

        final AbstractNumberMergeResult result =
            new AbstractNumberMergeResult(this, that);

        // If both are the same we can use that.
        final AbstractFloat resultVar;
        if (this.equals(that)) {
            resultVar = this;
        } else {
            resultVar = this.unknown();
        }
        result.setMergedVariable(resultVar);

        result.setVarAtoMerged(AbstractFloat.costForFloat(this, resultVar));
        result.setVarBtoMerged(AbstractFloat.costForFloat(that, resultVar));
        return result;
    }

    /**
     * Creates a new range by multiplying all values from this AbstractFloat by
     * all values from the argument.
     * @param n value to be multiplied
     * @return range of values obtained by multiplying values from this
     * AbstractFloat with values from n
     */
    public AbstractFloat mul(final AbstractFloat n) {
        return this.mul(n, false);
    }

    /**
     * Creates a new range from the product of two existing ranges.
     * @param n value to be added to this
     * @param isFPStrict flag indicating if this operation is done in fpstrict conditions.
     * @return product of this instance and the argument
     */
    public AbstractFloat mul(final AbstractFloat n, final boolean isFPStrict) {
        final double thisVal = this.literal;
        final double thatVal = n.literal;

        if (this.isLiteral() && n.isLiteral()) {
            /*
             * To handle strictness correctly, try to find out if there might be
             * a different (more exact) result. If that's the case, give out
             * an unknown value. Otherwise, give the (correct) value.
             */
            if (isFPStrict) {
                return AbstractFloat.create(thisVal * thatVal);
            } else {
                final double strictRes = this.mulStrict(thisVal, thatVal);
                final double exactRes = this.mulExact(thisVal, thatVal);

                if (strictRes == exactRes) {
                    return AbstractFloat.create(strictRes);
                }
            }
        }

        return this.unknown();
    }

    /**
     * @param one some double value.
     * @param two some double value.
     * @return multiplication result under strictfp conditions.
     */
    private double mulStrict(final double one, final double two) {
        return one * two;
    }

    /**
     * @param one some double value.
     * @param two some double value.
     * @return exact multiplication result, converted to double.
     */
    private double mulExact(final Double one, final Double two) {
        if (one.isNaN() || two.isNaN() || one.isInfinite() || two.isInfinite()) {
            return one * two;
        }
        final BigDecimal bOne = BigDecimal.valueOf(one);
        final BigDecimal bTwo = BigDecimal.valueOf(two);
        final BigDecimal res = bOne.multiply(bTwo);
        return res.doubleValue();
    }

    /**
    * Creates a new range by negating all values in this range. Take care that
    * with floats, this is not always -1 * this.
    * @return negated range
    */
    public AbstractFloat negate() {
        // For float values, negation is not the same as subtraction from zero.

        // This one should not depend on fpstrictness
        if (this.isLiteral()) {
            return AbstractFloat.create(-this.literal);
        }

        return this.unknown();
    }

    /**
     * Creates a new float which is the result of this % n.
     * @param n value to be multiplied
     * @param sameReference true iff both operands are the very same value.
     * @return the resulting float according to the JVMS for frem/drem.
     */
    public AbstractFloat rem(final AbstractFloat n, final boolean sameReference) {
        return this.rem(n, sameReference, false);
    }

    /**
     * Creates a new range from the remainder of two existing ranges.
     * @param n value to be added to this
     * @param sameReference true iff both operands are the very same value.
     * @param isFPStrict flag indicating if this operation is done in fpstrict conditions.
     * @return remainder of this instance and the argument
     */
    public AbstractFloat rem(final AbstractFloat n, final boolean sameReference, final boolean isFPStrict) {

        final double thisVal = this.literal;
        final double thatVal = n.literal;

        if (this.isLiteral() && n.isLiteral()) {
            /*
             * To handle strictness correctly, try to find out if there might be
             * a different (more exact) result. If that's the case, give out
             * an unknown value. Otherwise, give the (correct) value.
             */
            if (isFPStrict) {
                return AbstractFloat.create(thisVal % thatVal);
            } else {
                final double strictRes = this.remStrict(thisVal, thatVal);
                final double exactRes = this.remExact(thisVal, thatVal);

                if (strictRes == exactRes) {
                    return AbstractFloat.create(strictRes);
                }
            }
        }

        return this.unknown();
    }

    /**
     * @param one some double value.
     * @param two some double value.
     * @return remainder result under strictfp conditions.
     */
    private double remStrict(final double one, final double two) {
        return one % two;
    }

    /**
     * @param one some double value.
     * @param two some double value.
     * @return exact remainder result, converted to double.
     */
    private double remExact(final Double one, final Double two) {
        if (one.isNaN() || two.isNaN() || one.isInfinite() || two.isInfinite()) {
            return one % two;
        }
        final BigDecimal bOne = BigDecimal.valueOf(one);
        final BigDecimal bTwo = BigDecimal.valueOf(two);
        final BigDecimal res = bOne.remainder(bTwo);
        return res.doubleValue();
    }

    /**
     * Creates a new abstract float from the difference of two existing floats.
     * @param n value to be subtracted from this
     * @param sameReference set this if we are calculating x - x.
     * @param isFPStrict flag indicating if this operation is done in fpstrict conditions.
     * @return difference of this instance and the argument
     */
    public AbstractFloat sub(final AbstractFloat n, final boolean sameReference, final boolean isFPStrict) {
        return this.add(n.negate(), isFPStrict);
    }

    /**
     * @return String representation of this AbstractFloat.
     */
    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        if (this.isLiteral()) {
            sb.append(this.literal);
        } else {
            sb.append("#");
        }
        return sb.toString();
    }

    /**
     * @return the unknown float value which is wide iff this is wide
     */
    private AbstractFloat unknown() {
        return AbstractFloat.UNKNOWN;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result =
            prime
                * result
                + ((this.definedness == null) ? 0 : this.definedness.hashCode());
        result = prime * result + Double.hashCode(this.literal);
        return result;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public boolean equals(final Object obj) {
        if (this == obj) {
            return true;
        }
        if (obj == null) {
            return false;
        }
        if (this.getClass() != obj.getClass()) {
            return false;
        }
        final AbstractFloat other = (AbstractFloat) obj;
        if (this.definedness == null) {
            if (other.definedness != null) {
                return false;
            }
        } else if (!this.definedness.equals(other.definedness)) {
            return false;
        }
        if (Double.compare(this.literal, other.literal) != 0) {
            return false;
        }
        return true;
    }

    /**
     * @return true iff this is the unknown float/double
     */
    public boolean isUnknown() {
        return this == AbstractFloat.UNKNOWN;
    }

    /**
     * @return the literal value of this abstract float, if there is one.
     *  Undefined for non-literal floats!
     */
    public double getLiteral() {
        assert (this.definedness == Definedness.LITERAL);
        return this.literal;
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public AbstractNumber intersect(final AbstractNumber other)
            throws IntersectionFailException {
        if (!(other instanceof AbstractFloat)) {
            throw new IntersectionFailException("not a float: "
                + this.toString() + " " + other);
        }
        final AbstractFloat otherFloat = (AbstractFloat) other;
        if (this.isLiteral() && otherFloat.isLiteral()) {
            if (Double.isNaN(this.literal) && Double.isNaN(otherFloat.literal)) {
                return this;
            }
            if (this.literal != otherFloat.literal) {
                throw new IntersectionFailException("not the same literal: "
                    + this.toString() + " " + other);
            }
            return this;
        }
        if (this.isUnknown() && otherFloat.isLiteral()) {
            return otherFloat;
        }
        if (this.isLiteral() && otherFloat.isUnknown()) {
            return this;
        }
        if (this.isUnknown() && otherFloat.isUnknown()) {
            return this;
        }
        assert (false);
        throw new IntersectionFailException("fallthrough: " + this.toString()
            + " " + other);
    }

    @Override
    public Collection<String> toSExpStrings(final AbstractVariableReference ref) {
        if (this.isLiteral()) {
            String res = "(" + IntegerRelationType.EQ.toString() + " " + ref.toString() + " " + this.literal + ")";
            return Collections.singleton(res);
        } else {
            return Collections.emptyList();
        }
    }
}
