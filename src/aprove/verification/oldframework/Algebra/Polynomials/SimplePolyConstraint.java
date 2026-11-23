package aprove.verification.oldframework.Algebra.Polynomials;

import static aprove.verification.oldframework.Algebra.Polynomials.ConstraintType.*;

import java.math.*;
import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.diophantine.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.PredefinedFunction.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.domains.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBInt.SMTLIBIntComparison.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.SMTLIBRat.SMTLIBRatComparison.*;
import aprove.verification.oldframework.SMT.Expressions.*;
import aprove.verification.oldframework.SMT.Expressions.Sorts.*;
import aprove.verification.oldframework.SMT.Expressions.StaticBuilders.*;
import aprove.verification.oldframework.SMT.Utils.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Verifier.*;
import aprove.xml.*;
import immutables.*;


/**
 * @author Carsten Fuhs
 * @version $Id$
 *
 * A SimplePolyConstraint (abbrev.: SPC) encodes a SimplePolynomial
 * in relation with 0 where the relation is one of { =, >=, > }.
 * Use null for the unsatisfiable SimplePolyConstraint.
 *
 * The methods of this class rely on the assumption that "indefinites"
 * are supposed to be instantiated by non-negative numbers only.
 */
public class SimplePolyConstraint implements Immutable, Comparable<SimplePolyConstraint> {

    // the SimplePolynomial on the LHS of the constraint
    private final SimplePolynomial simplePoly;

    // the type of the Constraint; only ConstraintType.GE and ConstraintType.EQ
    // are possible/allowed values after object construction (ConstraintType.GT
    // should be transformed away by the constructor)
    private final ConstraintType type;

    private int hashValue; // cache for the hash value
    private boolean hashValid; // has the hash value already been computed?

    /**
     * Generate a new SimplePolyConstraint, using the parameters as values
     * for the attributes.
     *
     * @param simplePoly  the SimplePolynomial to occur on the LHS, non-null
     * @param type  the relation in which simplePoly is with 0, non-null
     */
    public SimplePolyConstraint(SimplePolynomial simplePoly, ConstraintType type) {
        if (Globals.useAssertions) {
            assert(simplePoly != null && type != null);
        }
        if (type == GT) {
            type = GE;
            simplePoly = simplePoly.plus(SimplePolynomial.MINUS_ONE);
        }
        this.simplePoly = simplePoly;
        this.type = type;
        this.hashValid = false;
    }


    /**
     * Convert simplePolyConstraint to an equivalent PolyConstraint
     * (without proper variables).
     *
     * @param simplePolyConstraint  to be converted to a Polynomial
     * @return a PolyConstraint which is equivalent to simplePolyConstraint
     */
    public static PolyConstraint toPolyConstraint(SimplePolyConstraint simplePolyConstraint) {
        Polynomial newPoly = SimplePolynomial.toPolynomial(simplePolyConstraint.simplePoly);
        int newType;
        switch (simplePolyConstraint.type) {
        case GE :
            newType = AbstractConstraint.GE;
            break;
        case EQ :
            newType = AbstractConstraint.EQ;
            break;
        default: // never to be reached
            newType = AbstractConstraint.DK;
            break;
        }
        return PolyConstraint.create(newPoly, newType);
    }


    /**
     * Convenience method for converting a Set of SimplePolyConstraints
     * to the corresponding Set of equivalent PolyConstraints (without
     * proper variables).
     *
     * @param simplePolyConstraints  to be converted
     * @return the corresponding equivalent PolyConstraints
     */
    public static Set<PolyConstraint> toPolyConstraints(Set<SimplePolyConstraint> simplePolyConstraints) {
        Set<PolyConstraint> result = new LinkedHashSet<PolyConstraint>();
        for (SimplePolyConstraint simplePolyConstraint : simplePolyConstraints) {
            result.add( SimplePolyConstraint.toPolyConstraint(simplePolyConstraint));
        }
        return result;
    }

    /**
     * @return the number of addends of the LHS polynomial
     */
    public int numberOfAddends() {
        return this.simplePoly.numberOfAddends();
    }


    /**
     * Return null if the LHS of this has a nonzero numerical addend; otherwise
     * return a Set of SimplePolyConstraint where for each IndefinitePart
     * of the LHS of this, a new one is generated with the same variables,
     * but exponents set to one, which is then used as a LHS of a
     * SimplePolyConstraint of type EQ.
     *
     * Applicable for simplifying a SimplePolyConstraint whose LHS
     * consists of simpleMonomials (addends) that only have negative factors
     * and which is of type GE (or EQ, in this case the sign of the factors
     * does not matter as long as it is constant over all addends of this).
     *
     * @return the Set of SimplePolyConstraints that follow from a
     * SimplePolyConstraint of type GE with this as LHS
     * where this.allNegative() == true or of type EQ with
     * (this.allPositive() || this.allNegative()) == true
     */
    Set<SimplePolyConstraint> addendsToConstraintsForConstantSign() {
        return this.simplePoly.addendsToConstraintsForConstantSign();
    }


    /**
     * @return whether all addends of the LHS of this have numerical
     * coefficients > 0 (true in case of the empty SimplePolynomial,
     * which is equal to 0)
     */
    boolean allPositive() {
        return this.simplePoly.allPositive();
    }


    /**
     * @return whether all addends of the LHS of this have numerical
     * coefficients < 0 (true in case of the empty SimplePolynomial,
     * which is equal to 0)
     */
    boolean allNegative() {
        return this.simplePoly.allNegative();
    }

    /**
     * @return a Set of all indefinites that occur in the LHS of this.
     */
    public Set<String> getIndefinites() {
        return this.simplePoly.getIndefinites();
    }

    /**
     * Convenience method to get the indefinites of a set of SPCs.
     *
     * @param spcs
     * @return
     */
    public static Set<String> getIndefinites(Iterable<? extends SimplePolyConstraint> spcs) {
        Set<String> result = new LinkedHashSet<String>();
        for (SimplePolyConstraint spc : spcs) {
            result.addAll( spc.getIndefinites() );
        }
        return result;
    }


    /**
     * Get the numerical addend of the LHS of this.
     *
     * @return the numerical addend of the LHS of this
     */
    BigInteger getNumericalAddend() {
        return this.simplePoly.getNumericalAddend();
    }

    /**
     * Simplifies a SimplePolyConstraint with one numerical and
     * one non-numerical addend.
     *
     * To be called /only/ if the LHS of this consists of one numerical and one
     * non-numerical addend, otherwise arbitrarily undesired behavior may occur.
     *
     * @return null if the numericalAddend modulo the factor of the
     * non-numerical addend is non-zero and this.type == EQ
     * (then the constraint is unsolvable);
     * a SimplePolyConstraint in which both numbers have been
     * "suitably" divided by the non-numerical addend otherwise
     * (multiplied with -1 in case of this.type == GE
     * and numerical addend > 0).
     */
    SimplePolyConstraint simplifyConstraintWithANumericalAndAnotherAddend() {
        return this.simplePoly.simplifyConstraintWithANumericalAndAnotherAddend(this.type);
    }


    /**
     * @return a Set of SimplePolyConstraints in which each a_i
     * occurring in the LHS of this is constrained to be > 0.
     */
    Set<SimplePolyConstraint> getConstraintsAllIndefinitesGT0() {
        return this.simplePoly.getConstraintsAllIndefinitesGT0();
    }


    /**
     * Computes the indefinite factors that occur in each of the addends
     * of the LHS of this together with their exponents.
     *
     * @return the IndefinitePart that encapsulates the common
     * indefinite factors of the LHS of this
     */
    IndefinitePart computeCommonFactors() {
        return this.simplePoly.computeCommonFactors();
    }

    /**
     * Computes the indefinite factors that occur in each of the addends
     * of the LHS of this together with their exponents reduced by one.
     *
     * @return the IndefinitePart that encapsulates the common
     * indefinite factors the LHS of this with their exponents reduced by one
     */
    public IndefinitePart computeCommonFactorsPowersMinusOne() {
        return this.simplePoly.computeCommonFactorsPowersMinusOne();
    }

    /**
     * Tries to divide the LHS of this by denominator.
     *
     * @param denominator the denominator by which we want to divide
     *  the LHS of this.
     * @return LHS of this / denominator if denominator | the LHS of this;
     *  otherwise, null is returned.
     */
    public SimplePolynomial divide(IndefinitePart denominator) {
        return this.simplePoly.divide(denominator);
    }


    /**
     * Divides the LHS of this by denominator with all its explicit exponents
     * treated as reduced by one and returns the resulting SimplePolynomial.
     *
     * It is *required* that denominator is a divisor of all addends of this,
     * the result is undefined otherwise (and Exceptions may occur).
     *
     * @param denominator  the denominator by which the LHS of this is to be
     *  "divided", must be a divisor of all addends of this
     * @return the resulting SimplePolynomial: this divided by denominator
     *  with its exponents treated as reduced by one before dividing
     */
    SimplePolynomial divideWithDenominatorPowersMinusOne(IndefinitePart denominator) {
        return this.simplePoly.divideWithDenominatorPowersMinusOne(denominator);
    }



    /**
     * @param zeroIndefinites  indefinites whose product is supposed to be
     *  equal to zero such that all addends of the LHS of this that contain all
     *  members of zeroIndefinites can be removed
     * @return the result of removing all addends that contain all the
     *  indefinites in zeroIndefinites from the LHS of this.
     */
    SimplePolyConstraint eliminateAddendsThatContainAll (Set<String> zeroIndefinites, Abortion aborter) throws AbortionException {
        SimplePolynomial resultingSimplePoly = this.simplePoly.eliminateAddendsThatContainAll(zeroIndefinites, aborter);
        return new SimplePolyConstraint(resultingSimplePoly, this.type);
    }

    SimplePolyConstraint specializeGENode(Map<String, GENode> specializationMap) {
        return new SimplePolyConstraint(this.simplePoly.specializeGENode(specializationMap),
                                        this.type);
    }


    /**
     * @return the type of this
     */
    public ConstraintType getType() {
        return this.type;
    }

    /**
     * Returns the polynomial
     * @return
     */
    public SimplePolynomial getPolynomial() {
        return this.simplePoly;
    }


    /**
     * Returns a version of this in which forbiddenIndefinites are replaced
     * by 1 in the LHS. Note that this method is only to be called if the
     * result of substituting forbiddenIndefinites by 1 will have as many
     * addends as the LHS of this, otherwise the result will probably be
     * semantically incorrect.
     * (a1*a2 + a1*a2^2 should become 2*a1 and not a1 as returned by this
     * method when called with a2 as parameter.)
     * Always safe to call if this only has one addend.
     *
     * @param forbiddenIndefinite  the indefinite to be removed from the
     *  addend(s) of this
     * @return the SimplePolyConstraint that results from omitting
     *  forbiddenIndefinites in the LHS of this and keeping the type
     */
    SimplePolyConstraint removeIndefinitesEfficiently(Set<String> forbiddenIndefinites) {
        return new SimplePolyConstraint(this.simplePoly.removeIndefinitesEfficiently(forbiddenIndefinites),
                                        this.type);
    }



    /**
     * Tries to simplify the LHS of this using eq2Constraint.
     * returns the result of this simplification.
     *
     * @param eq2Constraint  constraint which must be of the form
     *  a_i^l_i * ... * a_k^l_k - c = 0 with c \in N, to be used for
     *  simplifying this
     * @return a simplified version (possibly unsatisfiable) of this
     *  if such a simplification is possible, this otherwise.
     */
    SimplePolyConstraint applyEQ2(SimplePolyConstraint eq2Constraint) {
        if (Globals.useAssertions) {
            assert(eq2Constraint.type == EQ);
            assert(eq2Constraint.getPolynomial().numberOfAddends() == 2);
            for (IndefinitePart iPart : eq2Constraint.getPolynomial().getIndefiniteParts()) {
                if (! iPart.isEmpty()) {
                    assert(eq2Constraint.getPolynomial().getFactor(iPart).equals(BigInteger.ONE));
                }
            }
            assert(eq2Constraint.getPolynomial().getNumericalAddend().signum() != 0);
        }
        // get the IndefinitePart of eq2Constraint (we want to substitute it)
        IndefinitePart substituteMe = null;
        for (IndefinitePart candidate : eq2Constraint.simplePoly.getIndefiniteParts()) {
            if (! candidate.isEmpty()) {
                substituteMe = candidate;
                break; // found it, stop looking for more
            }
        }
        // get the number with which we want to substitute
        BigInteger replacement = eq2Constraint.getNumericalAddend().negate();
        // get the resulting, (possibly) simplified SimplePolynomial
        SimplePolynomial result = this.simplePoly.substitute(substituteMe,
                                                             replacement);

        return new SimplePolyConstraint(result, this.type);
    }

    /**
     * Performs some simple checks to see whether this is valid.
     *
     * @return true iff this is found to be valid
     *  (in case of doubt, false is returned)
     */
    public boolean isValid() {
        if ((this.type == GE) && (this.simplePoly.allPositive())) {
            return true;
        }
        if (this.simplePoly.isConstant()) {
            BigInteger value = this.simplePoly.getNumericalAddend();
            switch (this.type) {
            case EQ :
                return value.signum() == 0;
            case GE :
                return value.signum() >= 0;
            }
        }
        return false;
    }

    /**
     * Performs some simple checks to see whether this is satisfiable.
     *
     * @return true iff this is found to be satisfiable
     *  (in case of doubt, true is returned)
     */
    public boolean isSatisfiable() {
        if (this.simplePoly.isConstant()) {
            BigInteger value = this.simplePoly.getNumericalAddend();
            switch (this.type) {
            case EQ :
                if (value.signum() != 0) {
                    return false;
                }
            case GE :
                if (value.signum() < 0) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * @param mayChangeRelation  may we add/subtract 1 and use a
     *  different ConstraintType from the one of this in the result
     *  (e.g. GE -> GT)?
     *  false is highly recommended if this is a searchstrict constraint.
     * @return For this == p - q rel 0, rel \in {GE, EQ}, p,q without any
     *  negative factors, an equivalent representation (p', q', rel') is
     *  returned where p',q' do not contain any negative factors and where
     *  rel' \in {GE, EQ, GT}.
     */
    public Triple<SimplePolynomial, SimplePolynomial, ConstraintType> toPositiveForm(boolean mayChangeType) {

        SimplePolynomial oldPoly = this.simplePoly;
        ConstraintType resultType;

        final boolean ALWAYS_GE_TO_GT = false;
        // replace GE by GT, which is more suitable for propositional formulae
        if (ALWAYS_GE_TO_GT) {
            if (mayChangeType && this.type == GE) {
                resultType = GT;
                oldPoly = oldPoly.plus(SimplePolynomial.ONE);
            }
            else {
                resultType = this.type;
            }
        }
        // frequently occurring strong monotonicity constraints like
        // a_7 - 1 >= 0 should be encoded as a_7 > 0. Usually the other
        // GE-constraints have 0 as constant addend, so one should not
        // add anything and rather encode them as such.
        else {
            if (mayChangeType && this.type == GE &&
                    oldPoly.getNumericalAddend().equals(BigInteger.valueOf(-1))) {
                resultType = GT;
                oldPoly = oldPoly.plus(SimplePolynomial.ONE);
            }
            else {
                resultType = this.type;
            }
        }

        Pair<SimplePolynomial, SimplePolynomial> resultXY = oldPoly.toPositivePair();
        return new Triple<SimplePolynomial, SimplePolynomial, ConstraintType>(resultXY.x,
                resultXY.y, resultType);
    }

    /**
     * Checks whether <code>interpretation</code> satisfies this.
     * If some indefinites are not specified in interpretation, a
     * default value of <code>defaultValue</code> is used.
     *
     * @param interpretation mapping of indefinites to numbers
     * @param defaultValue the default value that shall be used for all
     *  those indefinites interpretation is not defined for
     * @return whether this is satisfied by interpretation
     */
    public boolean interpret(Map<String, BigInteger> interpretation, BigInteger defaultValue) {
        BigInteger value = this.simplePoly.interpret(interpretation, defaultValue);
        int comparisonResult = value.compareTo(BigInteger.ZERO);
        switch (this.type) {
        case EQ :
            return comparisonResult == 0;
        case GE :
            return comparisonResult >= 0;
        default :
            throw new RuntimeException("ConstraintType " + this.type +
                    " should not occur inside a SimplePolyConstraint!");
        }
    }

    /**
     * @return information that a certain variable is constrained to be
     *  with certain bounds if we manage to deduce it from this; null otherwise
     */
    public Pair<String, SearchBounds> toSearchBounds() {
        // examples for useful shapes are:
        // x - 42 >= 0, x + 17 = 0, x >= 0. x = 0
        // for now conveniently ignore gcd style deductions
        final Pair<GENode, GENode> geNodePair = this.simplePoly.toGENodePairForSearchBounds();
        if (geNodePair == null) {
            return null;
        }
        SearchBounds bound = null;
        String var = null;
        if (geNodePair.y.isNumerical()) { // useful!
            assert ! geNodePair.x.isNumerical();
            var = geNodePair.x.indefinite;
            BigInteger number = geNodePair.y.number;
            if (this.type == GE) {
                bound = SearchBounds.create(InfInt.create(number), InfInt.PLUS_INFINITY);
            } else if (this.type == EQ) {
                // have a interval of at least 2 elements, even if that's slightly less precise than we could
                bound = SearchBounds.create(InfInt.create(number.subtract(BigInteger.ONE)), InfInt.create(number));
            }
        } else if (geNodePair.x.isNumerical()) { // also nice
            assert ! geNodePair.y.isNumerical();
            var = geNodePair.y.indefinite;
            BigInteger number = geNodePair.x.number;
            if (this.type == GE) {
                bound = SearchBounds.create(InfInt.MINUS_INFINITY, InfInt.create(number));
            } else if (this.type == EQ) {
                // have a interval of at least 2 elements, even if that's slightly less precise than we could
                bound = SearchBounds.create(InfInt.create(number.subtract(BigInteger.ONE)), InfInt.create(number));
            }
        }
        if (var != null) {
            assert bound != null;
            return new Pair<String, SearchBounds>(var, bound);
        }
        return null;
    }


    public String toStringRep(PolyFormatter format) {
        StringBuilder b = new StringBuilder();
        if (this.type == EQ && format == PolyFormatter.RATSOLVER) {
            // quick hack as a workaround to deal with ratSolver
            // not handling equalities properly
            String polyRep = this.simplePoly.toStringRep(format);
            b.append(polyRep);
            b.append(">=0;\n0>=");
            b.append(polyRep);
        }
        else {
            b.append(this.simplePoly.toStringRep(format));
            b.append(this.type);
            b.append("0");
        }
        return b.toString();
    }

    /**
     * Primary criterion: The ConstraintType (fast!).
     * If there is a draw, compare the polys.
     *
     * @param other
     * @return
     */
    @Override
    public int compareTo(final SimplePolyConstraint other) {
        // EQ > GE; GT is illegal
        if (Globals.useAssertions) {
            assert other.type != GT;
        }
        if (this.type == EQ && other.type == GE) {
            return 1;
        }
        if (this.type == GE && other.type == EQ) {
            return -1;
        }
        if (Globals.useAssertions) {
            assert this.type == other.type;
        }

        // okay, we need to compare the polys
        return this.simplePoly.compareTo(other.simplePoly);
    }

    @Override
    public String toString() {
        StringBuilder result = new StringBuilder(this.simplePoly.toString());
        switch(this.type) {
        case GE:
            result.append(" >= 0");
            break;
        case EQ:
            result.append(" = 0");
            break;
        default:
            throw new RuntimeException("Illegal or unknown constraint type " + this.type);
        }
        return result.toString();
    }

    
    public SMTLIBTheoryAtom toSMTLIBRatTheoryAtom() {
        // 1. Build value
        final SMTLIBRatValue value =
            ToolBox.rewriteSimplePolynomialToSMTLIBRatValue(this.simplePoly);

        // 2. Build formula:
        switch (this.type) {
        case GE:
            return SMTLIBRatGE.create(value,
                SMTLIBRatConstant.create(BigInteger.ZERO));
        case EQ:
            return SMTLIBRatEquals.create(value,
                SMTLIBRatConstant.create(BigInteger.ZERO));
        case GT:
            return SMTLIBRatGT.create(value,
                SMTLIBRatConstant.create(BigInteger.ZERO));
        default:
            assert false;
            return null;
        }
    }
    
    public SMTLIBTheoryAtom toSMTLIBIntTheoryAtom() {
        // 1. Build value
        final SMTLIBIntValue value =
            ToolBox.rewriteSimplePolynomialToSMTLIBIntValue(this.simplePoly);

        // 2. Build formula:
        switch (this.type) {
        case GE:
            return SMTLIBIntGE.create(value,
                SMTLIBIntConstant.create(BigInteger.ZERO));
        case EQ:
            return SMTLIBIntEquals.create(value,
                SMTLIBIntConstant.create(BigInteger.ZERO));
        case GT:
            return SMTLIBIntGT.create(value,
                SMTLIBIntConstant.create(BigInteger.ZERO));
        default:
            assert false;
            return null;
        }
    }
    
    public SMTLIBIntCMP toSMTLIB() {
        final SMTLIBIntValue left, right;
        left = this.simplePoly.toSMTLIB();
        right = SMTLIBIntConstant.create(BigInteger.ZERO);
        switch (this.type) {
        case GE :
            return SMTLIBIntGE.create(left, right);
        case EQ :
            return SMTLIBIntEquals.create(left, right);
        default:
            throw new RuntimeException("Illegal or unknown constraint type " + this.type);
        }
    }

    public SMTExpression<SBool> toSMTExp(final VariableScope scope) {
        final SMTExpression<SInt> left, right;
        left = this.simplePoly.toSMT(scope);
        right = Ints.constant(0);
        switch (this.type) {
        case GE:
            return Ints.greaterEqual(left, right);
        case EQ:
            return Core.and(Ints.greaterEqual(left, right), Ints.lessEqual(left, right));
        default:
            throw new RuntimeException("Illegal or unknown constraint type " + this.type);
        }
    }

    @Override
    public int hashCode() {
        if (this.hashValid) {
            return this.hashValue;
        }
        this.computeHashValue();
        return this.hashValue;
    }

    private void computeHashValue() {
        this.hashValue = this.simplePoly.hashCode() + 2*this.type.hashCode();
        this.hashValid = true;
    }


    @Override
    public boolean equals(final Object o) {
        SimplePolyConstraint constraint;

        if (! (o instanceof SimplePolyConstraint)) {
            return false;
        }
        constraint = (SimplePolyConstraint) o;

        // profit from our cached hash value
        if (constraint.hashCode() != this.hashCode()) {
            return false;
        }
        return ( constraint.type.equals( this.type ) &&
                 constraint.simplePoly.equals( this.simplePoly ) );
    }


    public Element toDIODOM(Document doc, XMLMetaData xmlMetaData) {
        Element constraintTag = XMLTag.DIO_CONSTRAINT.createElement(doc);
        constraintTag.setAttribute("type",this.type.name());
        Element polynomialTag = this.simplePoly.toDIODOM(doc, xmlMetaData);
        constraintTag.appendChild(polynomialTag);
        return constraintTag;
    }

    public Boolean tryEvaluate(final Map<String, BigInteger> valueMap) {
        final BigInteger value = this.simplePoly.tryEvaluate(valueMap);

        if (value == null) {
            return null;
        }
        switch (this.type) {
        case GE:
            return value.compareTo(BigInteger.ZERO) >= 0;
        case EQ:
            return value.compareTo(BigInteger.ZERO) == 0;
        default:
            throw new RuntimeException("Illegal or unknown constraint type " + this.type);
        }
    }

    public SimplePolyConstraint replace(final Map<String, String> renamingMap) {
        return new SimplePolyConstraint(this.simplePoly.replace(renamingMap), this.type);
    }

    public TRSTerm toTerm() {
        return this.toTerm(IDPPredefinedMap.DEFAULT_MAP);
    }

    public TRSTerm toTerm(final IDPPredefinedMap predefined) {
        FunctionSymbol fs;

        switch (this.type) {
        case EQ:
            fs = predefined.getSym(Func.Eq, DomainFactory.INTEGERS);
            break;
        case GT:
            fs = predefined.getSym(Func.Gt, DomainFactory.INTEGERS);
            break;
        case GE:
            fs = predefined.getSym(Func.Gt, DomainFactory.INTEGERS);
            break;
        default:
            throw new RuntimeException("Illegal or unknown constraint type " + this.type);
        }

        return TRSTerm.createFunctionApplication(
            fs,
            this.getPolynomial().toTerm(),
            predefined.getIntTerm(BigIntImmutable.ZERO, DomainFactory.INTEGERS));
    }

}
