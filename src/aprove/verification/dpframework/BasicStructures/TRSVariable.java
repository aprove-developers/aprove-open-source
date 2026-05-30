/*
 * Created on 11.04.2005
 */
package aprove.verification.dpframework.BasicStructures;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.Globals.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Export.Utility.Export_Util.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * A TRSVariable is just a String. Nothing more.
 * @author thiemann
 */
public final class TRSVariable extends TRSTerm implements Variable {

    /**
     * Cache for hash value.
     */
    private final int hashCode;

    /**
     * The name.
     */
    private final String varName;

    /**
     * a Variable is constructed by a non-null string
     * @param name
     */
    protected TRSVariable(String name) {

// The following check is nice to have, but extremely costly in practice since we generate fresh variables all the
// time. Since we *always* enable assertions (even for the competition), I disabled it for now.

//        if (Globals.useAssertions) {
//            assert(name != null && !name.equals(""));
//            boolean isInt = true;
//            try {
//                Integer.parseInt(name);
//            } catch (NumberFormatException e) {
//                isInt = false;
//            }
//            assert(!isInt);
//        }
        this.varName = name;
        this.hashCode = name.hashCode() + 3829038;
    }

    @Override
    public void collectFunctionSymbols(Set<FunctionSymbol> fs) {
        // nothing todo here
    }

    @Override
    public void collectVariables(Set<TRSVariable> vars) {
        vars.add(this);
    }

    @Override
    public int compareTo(TRSTerm t) {
        if (t.isVariable()) {
            return this.varName.compareTo(((TRSVariable)t).varName);
        } else {
            return -1;
        }
    }

    @Override
    public void computeFunctionSymbolCount(Map<FunctionSymbol, Integer> map) {
        // nothing todo here
    }

    @Override
    public void computeVariableCount(Map<TRSVariable, Integer> map) {
        final Integer old = map.put(this, 1);
        if (old != null) {
            map.put(this, old + 1);
        }
    }

    @Override
    public boolean equals(Object other) {
        if (this == other) {
            return true;
        }
        if (other instanceof TRSVariable) {
            final TRSVariable v = (TRSVariable)other;
            return this.hashCode == v.hashCode && this.varName.equals(v.varName);
        }
        return false;
    }

    @Override
    public String export(Export_Util eu) {
        return this.export(eu, java.util.Collections.<TRSVariable>emptySet());
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String export(Export_Util eu, java.util.Collection<TRSVariable> freeVars) {
        final Color color;
        final boolean bold;
        if (Globals.aproveVersion == AproveVersion.DEVELOPER_VERSION
            && freeVars.contains(this)) {
            color = Color.GREEN;
            bold = true;
        } else {
            color = Color.RED;
            bold = false;
        }
        String[] splittedStr;
        // special variables: | is not permitted as part of a variable name in the TPDP.
        if (this.varName.contains("|")) {
            splittedStr = this.varName.split("[|]");

            // a variable of the form model|symbol is used for certain semantic labellings
            // Here, model is present in the output for verification.
            if (splittedStr.length == 2) {
                return eu.fontcolor(
                    eu.sup(eu.escape(splittedStr[0]))
                        + eu.escape(splittedStr[1]), color);
            }
        }
        final String result = eu.fontcolor(eu.escape(this.varName), color);
        if (bold) {
            return eu.bold(result);
        }
        return result;
    }

    @Override
    public Map<TRSVariable, TRSTerm> extendMatchingSubstitution(Map<TRSVariable, TRSTerm> sigma, TRSTerm that) {
        final TRSTerm thisSigma = sigma.get(this);
        if (thisSigma == null) {
            sigma.put(this, that);
            return sigma;
        } else {
            if (thisSigma.equals(that)) {
                return sigma;
            } else {
                return null;
            }
        }
    }

    @Override
    public int getDepth() {
        return 0;
    }

    @Override
    public int getDepthConstant() {
        return 0;
    }

    @Override
    public String getName() {
        return this.varName;
    }

    @Override
    public int getSize() {
        return 1;
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    @Override
    public boolean isConstant() {
        return false;
    }

    /**
     * @author Sebastian Weise
     */
    @Override
    public boolean isGroundTerm() {
        return false;
    }

    @Override
    public boolean isVariable() {
        return true;
    }

    @Override
    public boolean linearMatches(TRSTerm that) {
        return true;
    }

    @Override
    public TRSTerm processSubstitution(Substitution sigma) {
        return (TRSTerm)sigma.substitute(this);
    }

    @Override
    public TRSVariable renameVariables(aprove.verification.dpframework.BasicStructures.Utility.FreshVarGenerator gen) {
        return gen.getFreshVariable(this, true);
    }

    @Override
    public ImmutablePair<TRSVariable, Integer> renumberVariables(
        Map<TRSVariable, TRSVariable> map,
        String prefix,
        Integer initnr
        ) {
        int nr = initnr;
        TRSVariable replacement = map.get(this);
        if (replacement == null) {
            final String newName = prefix + nr;
            nr++;
            if (this.varName.equals(newName)) {
                replacement = this;
                map.put(this, replacement);
            } else {
                replacement = new TRSVariable(newName);
                map.put(this, replacement);
            }
        }
        return new ImmutablePair<TRSVariable, Integer>(replacement, nr);
    }

    @Override
    public TRSVariable renameAt(Position pos, FunctionSymbol replacement) {
        return this;
    }

    @Override
    public TRSVariable renameAtMap(Position pos, Map<FunctionSymbol, FunctionSymbol> replacements) {
        return this;
    }

    @Override
    public TRSVariable renameAtAllMap(Set<Position> poses, Map<FunctionSymbol, FunctionSymbol> replacements) {
        return this;
    }

    @Override
    public TRSTerm tcap(ImmutableSet<FunctionSymbol> definedSymbols, FreshNameGenerator fng) {
        return this;
    }

    @Override
    public Element toCPF2(Document doc, XMLMetaData xmlMetaData) {
        final Element var = CPFTag.VAR.createElement(doc);
        var.appendChild(doc.createTextNode(this.varName));
        return var;
    }

    @Override
    public Element toDOM2(Document doc, XMLMetaData xmlMetaData) {
        final Element e = XMLTag.VARIABLE.createElement(doc);
        XMLAttribute.VARNAME.setAttribute(e, this.varName);
        return e;
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String toTERMPTATION(FreshNameGenerator vars, FreshNameGenerator funcs) {
        return vars.getFreshName(this.getName(), true);
    }

    @Override
    protected void collectLeafPositions(Position pos, Collection<Position> pts) {
        pts.add(pos); // all variables are leaves
    }

    @Override
    protected void collectPositions(Position pos, Collection<Position> pts) {
        pts.add(pos);
    }

    @Override
    protected void collectPositionsAndSubTerms(
        Position pos,
        Collection<Pair<Position, TRSTerm>> pts,
        boolean dropRoot,
        boolean dropVars
    ) {
        if (dropRoot || dropVars) {
            // do nothing
        } else {
            pts.add(new Pair<Position, TRSTerm>(pos, this));
        }
    }
    
    @Override 
    protected void collectTree(Position pos, BiTreeNode<Pair<Position, TRSTerm>> parent) {
    	if (parent.getValue() == null) {
    		// root as leave
            parent.setValue(new Pair<>(pos, this));
    	} else {
    		parent.addChild(new BiTreeNode<>(new Pair<>(pos, this)));
    	}
    }

    @Override
    protected void collectSubTerms(Set<TRSTerm> subs, boolean dropVars) {
        if (dropVars) {
            // nothing to do
        } else {
            subs.add(this);
        }
    }

    @Override
    protected void collectVariablePositions(Position pos, Map<TRSVariable, List<Position>> varPositions) {
        List<Position> positions = varPositions.get(this);
        if (positions == null) {
            positions = new ArrayList<Position>();
            positions.add(pos);
            varPositions.put(this, positions);
        }
        else {
            positions.add(pos);
        }
    }

    @Override
    protected void computePathLabels(Position pos, int depth, List<FunctionSymbol> fs) {
        // nothing to do for variables
    }

    /**
     * help-method for the method "linearize(Variable)" in the super-class "Term"
     *
     * @author Sebastian Weise
     */
    @Override
    protected TRSTerm helpLinearize(TRSVariable variable, Set<TRSVariable> toAvoid) {
        if (!this.equals(variable)) {
            return this; // Term.createVariable(getName());
        } else {
            final TRSVariable result =
                (new aprove.verification.dpframework.BasicStructures.Utility.FreshVarGenerator(toAvoid)).getFreshVariable(
                    variable,
                    false);
            toAvoid.add(result);
            return result;
        }
    }

    @Override
    protected ImmutablePair<TRSTerm, Integer> icapQRst(
        QTermSet Q,
        Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR,
        TRSFunctionApplication s,
        Integer nr
    ) {
        return new ImmutablePair<TRSTerm, Integer>(this, nr);
    }

    @Override
    protected boolean isLinear(Set<TRSVariable> alreadyPresent) {
        return alreadyPresent.add(this);
    }

    @Override
    protected ImmutablePair<TRSTerm, Integer> tcap(
        Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR,
        Integer nr
    ) {
        return new ImmutablePair<TRSTerm, Integer>(new TRSVariable(TRSTerm.SECOND_STANDARD_PREFIX + nr), nr + 1);
    }

    @Override
    public ImmutablePair<TRSTerm, Integer> tcapE(
        Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR,
        Set<FunctionSymbol> ACs,
        Set<FunctionSymbol> Cs,
        Integer nr
    ) {
        return new ImmutablePair<TRSTerm, Integer>(new TRSVariable(TRSTerm.SECOND_STANDARD_PREFIX + nr), nr + 1);
    }

    @Override
    protected boolean testForLessVariables(Map<TRSVariable, Integer> map) {
        final int i = map.get(this);
        if (i == 0) {
            return false;
        } else {
            map.put(this, i - 1);
            return true;
        }
    }

    @Override
    public TRSTerm renameVariables(Map<TRSVariable, TRSVariable> map) {
        if (map.containsKey(this)) return map.get(this);
        else return this;
    }
    
    public int countAnnos(Set<FunctionSymbol> annoSyms) {
        return 0;
    }
    
    public Set<TRSFunctionApplication> getAnnoSubterms(Map<FunctionSymbol, FunctionSymbol> deAnnoMap) {
        Set<TRSFunctionApplication> res = new HashSet<TRSFunctionApplication>();

        return res;
    }
}
