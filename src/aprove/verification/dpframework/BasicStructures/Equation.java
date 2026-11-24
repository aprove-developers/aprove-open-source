/*
 * Created on 15.10.2005
 */
package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.xml.*;
import immutables.*;


/**
 * An equation is a pair of terms.
 *
 * Two equations are equal iff they are equal up to
 * symmetry or a variable renaming. Therefore we
 * store for each equation l == r its standard
 * representation in stdL == stdR.
 * 
 * Comment (Thieman): equality is not defined modulo symmetry!
 *
 * @author stein
 * @version $Id$
 */

public class Equation
    implements
        Immutable,
        HasFunctionSymbols,
        HasVariables,
        HasTRSTerms,
        HasTermPair,
        HTML_Able,
        XMLObligationExportable,
        CPFAdditional
{

    /*
     * real values
     */
    private final TRSTerm l, r;

    /*
     * computed values
     */
    private final TRSTerm stdL, stdR;
    private final int hashCode;


    private static boolean checkProperStd(final TRSTerm l, final TRSTerm stdL, final TRSTerm r, final TRSTerm stdR) {
        if (stdL == null || stdR == null) {
            return false;
        }

        TRSTerm stdLTest, stdRTest;
        Map<TRSVariable, TRSVariable> map = new HashMap<TRSVariable, TRSVariable>();
        final ImmutablePair<? extends TRSTerm, Integer> stdLAndInt1 = l.renumberVariables(map, TRSTerm.STANDARD_PREFIX, TRSTerm.STANDARD_NUMBER);
        final ImmutablePair<? extends TRSTerm, Integer> stdRAndInt1 = r.renumberVariables(map, TRSTerm.STANDARD_PREFIX, stdLAndInt1.y);
        map = new HashMap<TRSVariable, TRSVariable>();
        final ImmutablePair<? extends TRSTerm, Integer> stdRAndInt2 = r.renumberVariables(map, TRSTerm.STANDARD_PREFIX, TRSTerm.STANDARD_NUMBER);
        final ImmutablePair<? extends TRSTerm, Integer> stdLAndInt2 = l.renumberVariables(map, TRSTerm.STANDARD_PREFIX, stdRAndInt2.y);
        //compare stdLAndInt1.x == stdRAndInt1.x and stdLAndInt2.x == stdRAndInt2.x lexicographically
        // the smaller one is the standard representation
        if((stdLAndInt1.x.toString()+" == "+stdRAndInt1.x.toString()).compareTo(
            (stdRAndInt2.x.toString()+" == "+stdLAndInt2.x.toString())) < 0) {
            stdLTest = stdLAndInt1.x;
            stdRTest = stdRAndInt1.x;
        }
        else {
            stdLTest = stdRAndInt2.x;
            stdRTest = stdLAndInt2.x;
        }

        if (!stdLTest.equals(stdL)) {
            return false;
        }
        return stdRTest.equals(stdR);
    }

    /**
     * creates a new equation.
     * Restrictions: stdL is null iff stdR is null.
     *   If stdL is given, then stdL == stdR is the
     *   standard representation of l == r.
     *   In general as standard representation stdL == stdR
     *   we take the String representations of the variable
     *   renumbered l==r and r==l and take the lexicographically
     *   smaller one.
     * @param l - a term with the same variables as r
     * @param r - a term with the same variables as l
     * @param stdL - null or the lhs of the standard representation of l==r
     * @param stdR - null or the rhs of the standard representation of l==r
     */
    private Equation(final TRSTerm l, final TRSTerm r, TRSTerm stdL, TRSTerm stdR) {
        if (Globals.useAssertions) {
            assert (l != null) && (r != null);
            assert (stdL == null && stdR == null) || (stdL != null && stdR != null);
        }
        this.l = l;
        this.r = r;
        if (stdL == null) {
            Map<TRSVariable, TRSVariable> map = new HashMap<TRSVariable, TRSVariable>();
            final ImmutablePair<? extends TRSTerm, Integer> stdLAndInt1 = l.renumberVariables(map, TRSTerm.STANDARD_PREFIX, TRSTerm.STANDARD_NUMBER);
            final ImmutablePair<? extends TRSTerm, Integer> stdRAndInt1 = r.renumberVariables(map, TRSTerm.STANDARD_PREFIX, stdLAndInt1.y);
            map = new HashMap<TRSVariable, TRSVariable>();
            final ImmutablePair<? extends TRSTerm, Integer> stdRAndInt2 = r.renumberVariables(map, TRSTerm.STANDARD_PREFIX, TRSTerm.STANDARD_NUMBER);
            final ImmutablePair<? extends TRSTerm, Integer> stdLAndInt2 = l.renumberVariables(map, TRSTerm.STANDARD_PREFIX, stdRAndInt2.y);
            //compare stdLAndInt1.x == stdRAndInt1.x and stdLAndInt2.x == stdRAndInt2.x lexicographically
            // and take the smaller one als standard representation
            if((stdLAndInt1.x.toString()+" == "+stdRAndInt1.x.toString()).compareTo(
                (stdRAndInt2.x.toString()+" == "+stdLAndInt2.x.toString())) < 0) {
                stdL = stdLAndInt1.x;
                stdR = stdRAndInt1.x;
            }
            else {
                stdL = stdRAndInt2.x;
                stdR = stdLAndInt2.x;
            }
        }
        this.stdL = stdL;
        this.stdR = stdR;

        if (Globals.useAssertions) {
            assert(Equation.checkProperStd(this.l, this.stdL, this.r, this.stdR));
        }
        this.hashCode = 490321*stdL.hashCode() + 128127*stdR.hashCode() + 312038193;
    }

    /**
     * creates a new equation
     * @param l
     * @param r
     */
    public static Equation create(final TRSTerm l, final TRSTerm r) {
        return new Equation(l, r, null, null);
    }

    /**
     * creates a new commutative equation for the given binary function symbol with variables x and y
     */
    public static Equation createCEquation(final FunctionSymbol f) {
        final TRSTerm x = TRSTerm.createVariable("x");
        final TRSTerm y = TRSTerm.createVariable("y");
        final TRSTerm l = TRSTerm.createFunctionApplication(f,Equation.createArgArrayList(Arrays.asList(x,y)));
        final TRSTerm r = TRSTerm.createFunctionApplication(f,Equation.createArgArrayList(Arrays.asList(y,x)));
        return Equation.create(l,r);
    }

    /**
     * creates a new associative equation for the given binary function symbol with variables x, y and z
     */
    public static Equation createAEquation(final FunctionSymbol f) {
        final TRSTerm x = TRSTerm.createVariable("x");
        final TRSTerm y = TRSTerm.createVariable("y");
        final TRSTerm z = TRSTerm.createVariable("z");
        final TRSTerm l = TRSTerm.createFunctionApplication(f,Equation.createArgArrayList(Arrays.asList(
                TRSTerm.createFunctionApplication(f,Equation.createArgArrayList(Arrays.asList(x,y))),z)));
        final TRSTerm r = TRSTerm.createFunctionApplication(f,Equation.createArgArrayList(Arrays.asList(
                x,TRSTerm.createFunctionApplication(f,Equation.createArgArrayList(Arrays.asList(y,z))))));
        return Equation.create(l,r);
    }

    /**
     * creates a new sharped associative equation for the given binary function symbols F and f with variables x, y and z,
     * i.e. F(x, f(y, z)) == F(f(x, y), z)
     */
    public static Equation createSharpedAEquation(final FunctionSymbol F, final FunctionSymbol f) {
        final TRSTerm x = TRSTerm.createVariable("x");
        final TRSTerm y = TRSTerm.createVariable("y");
        final TRSTerm z = TRSTerm.createVariable("z");
        final TRSTerm l = TRSTerm.createFunctionApplication(F,Equation.createArgArrayList(Arrays.asList(
                TRSTerm.createFunctionApplication(f,Equation.createArgArrayList(Arrays.asList(x,y))),z)));
        final TRSTerm r = TRSTerm.createFunctionApplication(F,Equation.createArgArrayList(Arrays.asList(
                x,TRSTerm.createFunctionApplication(f,Equation.createArgArrayList(Arrays.asList(y,z))))));
        return Equation.create(l,r);
    }

    /**
     * Converts a List of something that extends Term into an ImmutableArrayList.
     * Helper function for Term construction. Use it as:
     * Term t = Term.createFunctionApplication(<FunctionSymbol>,createArgArrayList(Arrays.asList(<Term>,<Term>)));
     */
    public static ImmutableArrayList<TRSTerm> createArgArrayList(final List<? extends TRSTerm>argList) {
        final ArrayList<TRSTerm> argArrayList = new ArrayList<TRSTerm>();
        for(final TRSTerm arg : argList) {
            argArrayList.add(arg);
        }
        return ImmutableCreator.create(argArrayList);
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    /**
     * Equality is defined modulo variable renaming and symmetry.
     *
     * In the impl. this is done using a standard representation of an equation
     */
    public boolean equals(final Object other) {
        if (this == other) {
            return true;
        }
        if (other instanceof Equation) {
            final Equation eq = (Equation) other;
            return this.hashCode == eq.hashCode && this.stdL.equals(eq.stdL) && this.stdR.equals(eq.stdR);
        }
        return false;
    }

    /**
     * returns true iff this equation has identical variables.
     */
    public boolean checkIdenticalVariables() {
        return this.l.getVariables().containsAll(this.r.getVariables())
            && this.r.getVariables().containsAll(this.l.getVariables());
    }

    /**
     * returns true iff this equation has unique variables.
     */
    public boolean checkUniqueVariables() {
        return this.l.isLinear() && this.r.isLinear();
    }

    /**
     * returns true iff this equation has identical unique variables.
     */
    public boolean checkIdenticalUniqueVariables() {
        return this.checkIdenticalVariables()
                && this.checkUniqueVariables();
    }

    /**
     * returns true iff this equation is non collapsing.
     */
    public boolean checkNonCollapsing() {
        return !this.l.isVariable() && !this.r.isVariable();
    }

    /**
     * returns true iff this equation is a commutative one
     */
    public boolean checkCEquation() {
        if(this.getLeft() instanceof TRSFunctionApplication) {
            final FunctionSymbol f = ((TRSFunctionApplication)this.getLeft()).getRootSymbol();
            if (f.getArity() != 2) {
                return false;
            }
            final TRSTerm x = TRSTerm.createVariable("x");
            final TRSTerm y = TRSTerm.createVariable("y");
            final TRSTerm l = TRSTerm.createFunctionApplication(f,Equation.createArgArrayList(Arrays.asList(x,y)));
            final TRSTerm r = TRSTerm.createFunctionApplication(f,Equation.createArgArrayList(Arrays.asList(y,x)));
            final Equation cEquation = Equation.create(l,r);

            return this.equals(cEquation);
        }
        return false;
    }

    /**
     * returns true iff this equation is an associative one
     */
    public boolean checkAEquation() {
        if(this.getLeft() instanceof TRSFunctionApplication) {
            final FunctionSymbol f = ((TRSFunctionApplication)this.getLeft()).getRootSymbol();
            if (f.getArity() != 2) {
                return false;
            }
            final TRSTerm x = TRSTerm.createVariable("x");
            final TRSTerm y = TRSTerm.createVariable("y");
            final TRSTerm z = TRSTerm.createVariable("z");
            final TRSTerm l = TRSTerm.createFunctionApplication(f,Equation.createArgArrayList(Arrays.asList(
                    TRSTerm.createFunctionApplication(f,Equation.createArgArrayList(Arrays.asList(x,y))),z)));
            final TRSTerm r = TRSTerm.createFunctionApplication(f,Equation.createArgArrayList(Arrays.asList(
                    x,TRSTerm.createFunctionApplication(f,Equation.createArgArrayList(Arrays.asList(y,z))))));
            final Equation aEquation = Equation.create(l,r);

            return this.equals(aEquation);
        }
        return false;
    }

    /**
     * returns true iff this equation is a sharped associative one, e.g. lools like F(x,f(y,z)) = F(f(x,y),z)
     */
    public boolean checkSharpedAEquation() {
        if(this.getLeft() instanceof TRSFunctionApplication) {
            final FunctionSymbol F = ((TRSFunctionApplication)this.getLeft()).getRootSymbol();
            final Set<FunctionSymbol> fs = new HashSet<FunctionSymbol>(this.getFunctionSymbols());
            fs.remove(F);
            if(fs.size() == 1) {
                final FunctionSymbol f = fs.iterator().next();
                if (F.getArity() != 2 || f.getArity() != 2) {
                    return false;
                }
                final TRSTerm x = TRSTerm.createVariable("x");
                final TRSTerm y = TRSTerm.createVariable("y");
                final TRSTerm z = TRSTerm.createVariable("z");
                final TRSTerm l = TRSTerm.createFunctionApplication(F,Equation.createArgArrayList(Arrays.asList(
                        TRSTerm.createFunctionApplication(f,Equation.createArgArrayList(Arrays.asList(x,y))),z)));
                final TRSTerm r = TRSTerm.createFunctionApplication(F,Equation.createArgArrayList(Arrays.asList(
                        x,TRSTerm.createFunctionApplication(f,Equation.createArgArrayList(Arrays.asList(y,z))))));
                final Equation aSharpEquation = Equation.create(l,r);

                return this.equals(aSharpEquation);
            }
        }
        return false;
    }

    /**
     * returns the lhs
     */
    public TRSTerm getLeft() {
        return this.l;
    }

    /**
     * returns the rhs.
     */
    public TRSTerm getRight() {
        return this.r;
    }

    /**
     * returns the set of terms occurring in this equation,
     * i.e. {l,r}
     */
    @Override
    public Set<TRSTerm> getTerms() {
        final Set<TRSTerm> res = new LinkedHashSet<TRSTerm>();
        res.add(this.l);
        res.add(this.r);
        return res;
    }

    /**
     * returns the set of variables occurring in this equation
     */
    @Override
    public Set<TRSVariable> getVariables() {
        final Set<TRSVariable> leftVars = this.l.getVariables();
        leftVars.addAll(this.r.getVariables());
        return leftVars;
    }

    /**
     * returns the set of functionSymbols occurring in this equation
     */
    @Override
    public ImmutableSet<FunctionSymbol> getFunctionSymbols() {
        final Set<FunctionSymbol> fs = new LinkedHashSet<FunctionSymbol>(this.l.getFunctionSymbols());
        fs.addAll(this.r.getFunctionSymbols());
        return ImmutableCreator.create(fs);
    }

    /**
     * get the set of root symbols of the given Set of Equations
     * the resulting set may be modified!
     * Equivalent method to Collection.getRootSymbols for a Set of Rules
     */
    public static Set<FunctionSymbol> getRootSymbols(final Set<Equation> rs) {
        final Set<FunctionSymbol> fs = new LinkedHashSet<FunctionSymbol>();
        for (final Equation r : rs) {
            fs.addAll(r.getRootSymbols());
        }
        return fs;
    }

    /**
     * returns the set of functionSymbols occurring at a root position in this equation
     */
    public ImmutableSet<FunctionSymbol> getRootSymbols() {
        final Set<FunctionSymbol> fs = new LinkedHashSet<FunctionSymbol>();
        if(!this.l.isVariable()) {
            fs.add(((TRSFunctionApplication)this.l).getRootSymbol());
        }
        if(!this.r.isVariable()) {
            fs.add(((TRSFunctionApplication)this.r).getRootSymbol());
        }
        return ImmutableCreator.create(fs);
    }

    /**
     * returns the lhs of the standardRepresentation.
     * (constant time)
     */
    public TRSTerm getLhsOfStandardRepresentation() {
        return this.stdL;
    }

    /**
     * returns the rhs of the standardRepresentation.
     * (constant time)
     */
    public TRSTerm getRhsOfStandardRepresentation() {
        return this.stdR;
    }

    /**
     * returns a standard representation of this
     * equation where l = stdL and r = stdR.
     * (constant time)
     */
    public Equation getStandardRepresentation() {
        return new Equation(this.stdL, this.stdR, this.stdL, this.stdR);
    }
    
    public Equation renameVariables(final Collection<TRSVariable> forbidden) {
        final aprove.verification.dpframework.BasicStructures.Utility.FreshVarGenerator gen = new aprove.verification.dpframework.BasicStructures.Utility.FreshVarGenerator(forbidden);
        final TRSTerm newLeft = this.l.renameVariables(gen);
        final TRSTerm newRight = this.r.renameVariables(gen);
        return new Equation(newLeft, newRight, this.stdL, this.stdR);
    }

    public String export(final Export_Util eu) {
        return this.getLeft().export(eu) + " == " + this.getRight().export(eu);
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {

        final Element equTag = XMLTag.EQUATION.createElement(doc);
        equTag.appendChild(this.l.toDOM(doc, xmlMetaData));
        equTag.appendChild(this.r.toDOM(doc, xmlMetaData));
        return equTag;
    }

    @Override
    public Element toCPF(final Document doc, final XMLMetaData xmlMetaData) {
        final Element equTag = CPFTag.EQUATION_STEP.createElement(doc);
        equTag.appendChild(this.l.toDOM(doc, xmlMetaData));
        equTag.appendChild(this.r.toDOM(doc, xmlMetaData));
        return equTag;
    }

    public Element toCPFasRule(final Document doc, final XMLMetaData xmlMetaData) {
        final Element equTag = CPFTag.RULE.createElement(doc);
        equTag.appendChild(CPFTag.LHS.create(doc, this.l.toCPF(doc, xmlMetaData)));
        equTag.appendChild(CPFTag.RHS.create(doc, this.r.toCPF(doc, xmlMetaData)));
        return equTag;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String toHTML() {
        return this.export(new HTML_Util());
    }

}
