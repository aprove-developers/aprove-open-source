/*
 * Created on 11.04.2005
 */
package aprove.verification.dpframework.BasicStructures;

import java.math.*;
import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;
import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.Unification.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.xml.*;
import immutables.*;

/**
 * A TRSTerm is a TRSVariable or a TRSFunctionApplication and nothing else!
 * There are no sorts, types, ConstructorApplications, ...
 * @author thiemann
 * @see TRSFunctionApplication
 * @see TRSVariable
 */
public abstract class TRSTerm
    implements
    Expression,
    XMLObligationExportable,
    CPFAdditional,
    HasFunctionSymbols,
    Comparable<TRSTerm>,
    Iterable<TRSTerm> {

    /**
     * An empty array list provided for convenience and optimization for all those FunctionApplications of arity 0.
     */
    public final static ImmutableArrayList<TRSTerm> EMPTY_ARGS = ImmutableCreator.create(new ArrayList<TRSTerm>(0));

    /**
     * Second default prefix for variables.
     */
    public final static String SECOND_STANDARD_PREFIX = "y";

    /**
     * The default number.
     */
    public final static int STANDARD_NUMBER = 0;

    /**
     * Default prefix for variables. All these prefixes have to be different!
     */
    public final static String STANDARD_PREFIX = "x";

    /**
     * Third default prefix for variables.
     */
    public final static String THIRD_STANDARD_PREFIX = "z";

    /**
     * @param f A symbol with arity n.
     * @param args A list of arity n where all arguments are non-null.
     * @return A new Function Application from the arguments.
     */
    public static TRSFunctionApplication createFunctionApplication(
        FunctionSymbol f,
        ImmutableList<? extends TRSTerm> args) {
        if (f.getArity() == 0) {
            if (Globals.useAssertions) {
                assert (args.isEmpty()) : "Size of arguments does not match arity!";
            }
            return new TRSConstantTerm(f);
        }
        return new TRSCompoundTerm(f, args);
    }

    /**
     * @param f A symbol with arity n.
     * @param args A list of arity n where all arguments are non-null; MUST NOT be modified after invoking this method!
     * @return A new Function Application from the arguments.
     */
    public static TRSFunctionApplication createFunctionApplication(
        FunctionSymbol f,
        List<? extends TRSTerm> args) {
        return TRSTerm.createFunctionApplication(f, ImmutableCreator.create(args));
    }

    /**
     * @param f A symbol with arity n.
     * @param args An array of arity n where all arguments are non-null.
     * @return A new Function Application from the arguments.
     */
    public static TRSFunctionApplication createFunctionApplication(FunctionSymbol f, TRSTerm... args) {
        if (f.getArity() == 0) {
            if (Globals.useAssertions) {
                assert (args.length == 0) : "Number of arguments does not match arity!";
            }
            return new TRSConstantTerm(f);
        }
        final ArrayList<TRSTerm> v = new ArrayList<TRSTerm>(args.length);
        for (TRSTerm t : args) {
            v.add(t);
        }
        return new TRSCompoundTerm(f, ImmutableCreator.create(v));
    }

    /**
     * Create a constant term
     * @param value The value the constant term shall have
     * @return A new constant term with that value
     */
    public static TRSConstantTerm createConstant(String value) {
        FunctionSymbol functionSymbol = FunctionSymbol.create(value, 0);
        return new TRSConstantTerm(functionSymbol);
    }

    /**
     * @param name A non-null string.
     * @return A new Variable.
     */
    public static TRSVariable createVariable(String name) {
        return new TRSVariable(name);
    }

    /**
     * computes icapQRs(t). Returns t if icapQRs(t) = t (same object)
     * the variables introduces by icap are taken from SECOND_STANDARD_PREFIX.
     * It is required that the lhs of R are in STANDARD_RENUMBERED format.
     * Moreover, s_to_t has to be in THIRD_STANDARD_PREFIX.
     * This requirements are to ensure correct unification of
     * variable disjoint terms without making all terms variable disjoint!
     * @param Q
     * @param lhsR - a map from function symbols to lhs with corresponding root symbol
     * @param s_to_t
     * @return a term only where all variables are from SECOND/THIRD_STANDARD_PREFIX
     */
    public static final TRSTerm icapQRst(
        QTermSet Q,
        Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR,
        Rule s_to_t) {
        if (Globals.useAssertions) {
            assert (s_to_t.checkVariablePrefix(TRSTerm.THIRD_STANDARD_PREFIX));
            assert (TRSTerm.icapAssertCheck(Q, lhsR));
        }
        final TRSTerm t = s_to_t.getRight();
        if (lhsR.isEmpty()) {
            return t;
        }
        // this implies that Q is non-empty, too!
        // because otherwise Q could not rewrite any rule from lhsR
        final ImmutablePair<TRSTerm, Integer> res = t.icapQRst(Q, lhsR, s_to_t.getLeft(), TRSTerm.STANDARD_NUMBER);
        if (Globals.useAssertions) {
            assert (t == res.x || !t.equals(res.x));
        }
        return res.x;
    }

    /**
     * @param lhsR The lhss for R.
     * @return True if the lhss are in standard renumbered format. False otherwise.
     */
    static final boolean tcapAssertCheck(Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR) {
        if (lhsR == null) {
            return false;
        }
        for (Set<TRSFunctionApplication> lhss : lhsR.values()) {
            for (TRSFunctionApplication lhs : lhss) {
                //
                if (!lhs.equals(lhs.getStandardRenumbered())) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * @param Q The set Q.
     * @param lhsR The lhss of R.
     * @return True if Q normal implies R normal and the rules are in standard renumbered format. False otherwise.
     */
    private static boolean icapAssertCheck(QTermSet Q, Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR) {
        for (Set<TRSFunctionApplication> lhss : lhsR.values()) {
            for (TRSFunctionApplication lhs : lhss) {
                // check that we really have Q normal implies R normal
                if (!Q.canBeRewritten(lhs)) {
                    return false;
                }
                // check that the rules are in standard renumbered format
                if (!lhs.equals(lhs.getStandardRenumbered())) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * Default constructor.
     */
    protected TRSTerm() {
        // empty
    }

    @Override
    public TRSTerm applySubstitution(Substitution sigma) {
        if (sigma instanceof TRSSubstitution) {
            if (((TRSSubstitution) sigma).isEmpty()) {
                return this;
            }
        }
        return this.processSubstitution(sigma);
    }

    /**
     * @param prefix Some prefix.
     * @return True if the name of every variable in this term starts with the string prefix.
     */
    public boolean checkVariablePrefix(String prefix) {
        for (TRSVariable v : this.getVariables()) {
            if (!v.getName().startsWith(prefix)) {
                return false;
            }
        }
        return true;
    }

    /**
     * adds all the function symbols occurring in this term to the set fs
     * @param fs
     */
    public abstract void collectFunctionSymbols(Set<FunctionSymbol> fs);

    /**
     * adds all the variables occurring in this term to the set vars
     * @param vars
     */
    public abstract void collectVariables(Set<TRSVariable> vars);

    /**
     * adds all variables occurring in this term to the map where
     * occurrences counts.
     * @param map
     */
    public abstract void computeFunctionSymbolCount(Map<FunctionSymbol, Integer> map);

    /**
     * adds all variables occurring in this term to the map where
     * occurrences counts.
     * @param map
     */
    public abstract void computeVariableCount(Map<TRSVariable, Integer> map);

    /**
     * @param var Some variable.
     * @return True iff "var" is contained in the term more than once;
     *         "var" does not need to be contained in the term (then, of course, false is returned).
     * @author Sebastian Weise
     */
    public boolean containsMoreThanOnce(TRSVariable var) {
        final List<Position> positions = this.getVariablePositions().get(var);
        if (positions == null) {
            return false;
        }
        return positions.size() >= 2;
    }

    /**
     * @param eu the export util
     * @param freeVars variables of this term which are contained in this set
     * may be printed differently
     * @return a string representation of this term
     */
    public abstract String export(Export_Util eu, java.util.Collection<TRSVariable> freeVars);

    /**
     * extends the substitution sigma to some sigma' such that
     * that. Here extension means that sigma(x) = sigma'(x) for all x in
     * keyset(sigma). If such a sigma' exists we return sigma', otherwise null.
     * sigma itself will / may be modified!
     * @param sigma Some substitution.
     * @param that Some term.
     * @return
     */
    public abstract Map<TRSVariable, TRSTerm> extendMatchingSubstitution(Map<TRSVariable, TRSTerm> sigma, TRSTerm that);

    /**
     * return the maximal depth of a term where a constant has depth 0!
     */
    public abstract int getDepth();

    /**
     * return the maximal depth of a term where a constant has depth 1!
     */
    public abstract int getDepthConstant();

    /**
     * returns a map from function symbols of this to their number
     * of occurrences
     * @return
     */
    public final Map<FunctionSymbol, Integer> getFunctionSymbolCount() {
        final Map<FunctionSymbol, Integer> result = new LinkedHashMap<FunctionSymbol, Integer>();
        this.computeFunctionSymbolCount(result);
        return result;
    }

    /**
     * returns the set of function symbols occuring in this term.
     * This set may be modified
     */
    @Override
    public final Set<FunctionSymbol> getFunctionSymbols() {
        final Set<FunctionSymbol> fs = new LinkedHashSet<FunctionSymbol>();
        this.collectFunctionSymbols(fs);
        return fs;
    }

    /**
     * @return the set of all positions in the term that
     *  have no proper prefix in this; you may modify the result set
     */
    public final Set<Position> getLeafPositions() {
        final Set<Position> pts = new LinkedHashSet<Position>();
        this.collectLeafPositions(Position.create(), pts);
        return pts;
    }

    /**
     * docu-guess (fuhs):
     * Returns the longest prefix p of pos such that root(t|p)
     * is a function symbol (and well-defined, of course).
     *
     * @return
     */
    public final Position getLongestPrefixInTerm(Position pos) {
        if (Globals.useAssertions) {
            assert (pos != null);
        }
        if (pos.isEmptyPosition()) {
            return pos;
        }
        final int[] posArray = pos.toIntArray();
        TRSTerm actTerm = this;
        int depth = 0;
        while (depth < posArray.length && !actTerm.isVariable()) {
            final TRSFunctionApplication fa = (TRSFunctionApplication) actTerm;
            if (posArray[depth] < fa.getRootSymbol().getArity()) {
                actTerm = fa.getArgument(posArray[depth]);
                depth++;
            } else {
                break;
            }
        }
        if (depth == 0) {
            return Position.create();
        } else if (depth == posArray.length) {
            return pos;
        } else {
            final int[] res = new int[depth];
            /* Why arraycopy doesn't work? counterexample: posArray = [3,0], depth = 1 results res = [0] */
            //System.arraycopy(posArray, 0, res, 0, depth - 1);
            for (int i = 0; i < depth; ++i) {
                res[i] = posArray[i];
            }
            return Position.create(res);
        }
    }

    /**
     * returns the matcher of this and that if it exists, and null otherwise.     *
     * @param that
     * @return
     * @see matches
     */
    public final TRSSubstitution getMatcher(TRSTerm that) {
        Map<TRSVariable, TRSTerm> sigma = new LinkedHashMap<TRSVariable, TRSTerm>();
        sigma = this.extendMatchingSubstitution(sigma, that);
        if (sigma == null) {
            return null;
        } else {
            return TRSSubstitution.create(ImmutableCreator.create(sigma));
        }
    }

    /**
     * returns null, if terms are not unifiable. returns the mgu of this and
     * returns the mgu of this and that, otherwise.
     * @param other
     * @return
     */
    public final TRSSubstitution getMGU(TRSTerm that) {
        return new Unification(this, that).getMgu();
    }

    /**
     * @return The set of all non-root and non-variable positions with its corresponding subterms.
     */
    @SuppressWarnings({ "rawtypes", "unchecked" })
    public final Collection<Pair<Position, TRSFunctionApplication>> getNonRootNonVariablePositionsWithSubTerms() {
        final Collection<Pair<Position, TRSFunctionApplication>> pts =
            new ArrayList<Pair<Position, TRSFunctionApplication>>();
        // cast to rawtype necessary since type inference for nested generic types is broken
        this.collectPositionsAndSubTerms(Position.create(), (Collection) pts, true, true);
        return pts;
    }

    /**
     * @return The set of non-variable subterms of this term. The set may be modified.
     */
    @SuppressWarnings({ "rawtypes", "unchecked" })
    public final Set<TRSFunctionApplication> getNonVariableSubTerms() {
        final Set<TRSFunctionApplication> res = new LinkedHashSet<TRSFunctionApplication>();
        // cast to rawtype necessary since type inference for nested generic types is broken
        this.collectSubTerms((Set) res, true);
        return res;
    }

    /**
     * @param pos
     * @return the list of function symbols one sees when going to pos in this
     *  starting from the empty position (to be precise, when going to the
     *  longest prefix of pos that is still in this); you may modify the
     *  result list
     */
    public final ArrayList<FunctionSymbol> getPathLabels(Position pos) {
        final ArrayList<FunctionSymbol> fs = new ArrayList<FunctionSymbol>(pos.getDepth());
        this.computePathLabels(pos, 0, fs);
        return fs;
    }

    /**
     * returns the set of all positions in the term
     * @return
     */
    public final Set<Position> getPositions() {
        final Set<Position> pts = new LinkedHashSet<Position>();
        this.collectPositions(Position.create(), pts);
        return pts;
    }

    /**
     * returns the set of all positions in the term with its corresponding subterms
     * @return
     */
    public final Collection<Pair<Position, TRSTerm>> getPositionsWithSubTerms() {
        final Collection<Pair<Position, TRSTerm>> pts = new ArrayList<Pair<Position, TRSTerm>>();
        this.collectPositionsAndSubTerms(Position.create(), pts, false, false);
        return pts;
    }

    /**
     * returns the tree representation of the term
     * @return
     */
    public BiTreeNode<Pair<Position, TRSTerm>> getTreeRep() {
        final BiTreeNode<Pair<Position, TRSTerm>> tree = new BiTreeNode<Pair<Position, TRSTerm>>(null);
        this.collectTree(Position.create(), tree);
        return tree;
    }

    abstract void collectTree(Position pos, BiTreeNode<Pair<Position, TRSTerm>> parent);

    /**
     * checks whether this and that are semiunifiable and generates a pair of substitutions
     * as a solution where pair.x is the matcher and pair.y is the semiunifier
     * @param that
     * @return
     */
    public Pair<TRSSubstitution, TRSSubstitution> getSemiSubstitutions(TRSTerm that) {
        return new SemiUnification(this, that).getSubstitutions();
    }

    /**
     * return the absolute number of variables and function symbols in a term.
     */
    public abstract int getSize();

    /**
     * returns the term where we renumber the variables with the STANDARD_PREFIX.
     * @see renumberVariables
     * @return
     */
    public final TRSTerm getStandardRenumbered() {
        return this.renumberVariables(new HashMap<TRSVariable, TRSVariable>(), TRSTerm.STANDARD_PREFIX, TRSTerm.STANDARD_NUMBER).x;
    }

    /**
     * This method eturns the subterm of this term at position <code>pos</code>.
     * The caller has to ensure that <code>pos</code> is a valid position of this term.
     * @param pos
     * @return
     */
    public final TRSTerm getSubterm(Position pos) {
        if (Globals.useAssertions) {
            assert (pos != null);
        }
        if (pos.isEmptyPosition()) {
            return this;
        }
        final int[] posArray = pos.toIntArray();
        TRSTerm actTerm = this;
        TRSFunctionApplication actFunc = (TRSFunctionApplication) this;
        final int toDepth = posArray.length;
        for (int i = 0; i < toDepth - 1; i++) {
            actTerm = actFunc.getArgument(posArray[i]);
            actFunc = (TRSFunctionApplication) actTerm;
        }
        if (toDepth > 0) {
            actTerm = actFunc.getArgument(posArray[toDepth - 1]);
        }
        return actTerm;
    }

    /**
     * This method eturns the subterm of this term at position <code>pos</code>.
     * The caller has not to ensure that <code>pos</code> is a valid position of this term.
     * it returns null for invalid positions
     * @param pos
     * @return
     */
    public final TRSTerm getSubtermOrNull(Position pos) {
        if (Globals.useAssertions) {
            assert (pos != null);
        }
        if (pos.isEmptyPosition()) {
            return this;
        }
        final int[] posArray = pos.toIntArray();
        TRSTerm actTerm = this;
        TRSFunctionApplication actFunc;
        for (int i = 0; i < pos.getDepth(); i++) {
            if (actTerm.isVariable()) {
                return null;
            }
            actFunc = (TRSFunctionApplication) actTerm;
            final int p = posArray[i];
            if (p >= actFunc.getRootSymbol().getArity()) {
                return null;
            }
            actTerm = actFunc.getArgument(p);
        }
        return actTerm;
    }

    /**
     * returns the set of subterms of this term.
     * The set may be modified
     * @return
     */
    public final Set<TRSTerm> getSubTerms() {
        final Set<TRSTerm> subs = new LinkedHashSet<TRSTerm>();
        this.collectSubTerms(subs, false);
        return subs;
    }

    /**
     * returns a map from variables of this to their nr of occurence
     * @return
     */
    public final Map<TRSVariable, Integer> getVariableCount() {
        final Map<TRSVariable, Integer> result = new LinkedHashMap<TRSVariable, Integer>();
        this.computeVariableCount(result);
        return result;
    }

    /**
     * @return this.containsVariablesAsOften(that) returns true  iff 
     * the list for each variable of this is at least as long as the list for each variable of that
     */
    public final boolean containsVariablesAsOften(Map<TRSVariable, List<Position>> that) {
        for (Entry<TRSVariable, List<Position>> entry : that.entrySet()) {
            if (this.getVariables().contains(entry.getKey())) {
                if (this.getVariablePositions().get(entry.getKey()).size() < entry.getValue().size()) {
                    return false;
                }
            } else {
                return false;
            }
            
        }
        return true;
    }

    /**
     * @return a map which stores for the occurring variables
     *  at which positions they occur
     */
    public final Map<TRSVariable, List<Position>> getVariablePositions() {
        final Map<TRSVariable, List<Position>> vps = new LinkedHashMap<TRSVariable, List<Position>>();
        this.collectVariablePositions(Position.create(), vps);
        return vps;
    }

    @Override
    public final Set<TRSVariable> getVariables() {
        final Set<TRSVariable> vars = new LinkedHashSet<TRSVariable>();
        this.collectVariables(vars);
        return vars;
    }

    /**
     * checks whether for each variable of this term the nr of occurrences in
     * this term is not larger than the number given in the map. Requires that
     * the map contains values >= 0 for all variables of this term. This method
     *
     * @return
     */
    public final boolean hasLessVariablesThan(Map<TRSVariable, Integer> map) {
        return this.testForLessVariables(map);
    }

    /**
     * checks whether this term has sub as proper subterm, i.e. whether there is some
     * non-empty position p such that this|_p = sub.
     */
    public final boolean hasProperSubterm(TRSTerm sub) {
        if (Globals.useAssertions) {
            assert (sub != null);
        }
        if (this.isVariable()) {
            return false;
        }

        for (TRSTerm arg : ((TRSFunctionApplication) this).getArguments()) {
            if (arg.hasSubterm(sub)) {
                return true;
            }
        }

        return false;
    }

    /**
     * checks whether this term has sub as a subterm, i.e. whether there is some
     * position p such that this|_p = sub. This method is equivalent to
     *
     * This method is equivalent to this.getSubterms.contains(sub), but it
     * @param sub
     * @return
     */
    public final boolean hasSubterm(TRSTerm sub) {
        if (Globals.useAssertions) {
            assert (sub != null);
        }
        if (this.equals(sub)) {
            return true;
        }
        if (this.isVariable()) {
            return false;
        }

        for (TRSTerm arg : ((TRSFunctionApplication) this).getArguments()) {
            if (arg.hasSubterm(sub)) {
                return true;
            }
        }

        return false;
    }

    public abstract boolean isConstant();

    /**
     * @author Sebastian Weise
     */
    public abstract boolean isGroundTerm();

    /**
     * checks whether a term is linear, i.e., whether it does not contain
     * some variable twice.
     * @return
     */
    public final boolean isLinear() {
        return this.isLinear(new HashSet<TRSVariable>());
    }

    /**
     * checks if this term is normal with respect to <code>setOfRules</code>
     */
    public boolean isNormal(Set<? extends RuleSchema> setOfRules) {
        for (Pair<Position, TRSTerm> posTerm : this.getPositionsWithSubTerms()) {
            final TRSTerm actSubterm = posTerm.y;
            for (RuleSchema actRule : setOfRules) {
                if (actRule.getLeft().matches(actSubterm)) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * checks if all of the proper subterms are in normal with respect to <code>setOfRules</code>
     */
    public boolean areAllProperSubtermsInNormal(Set<? extends RuleSchema> setOfRules) {
        Set<TRSTerm> allProperSubterms = this.getSubTerms();
        allProperSubterms.remove(this);
        for (TRSTerm subterm : allProperSubterms) {
            if (!subterm.isNormal(setOfRules)) {
                return false;
            }
        }
        return true;
    }

    public abstract boolean isVariable();

    /**
     * Iterates over a term, top-to-bottom, left-to-right.
     */
    @Override
    public Iterator<TRSTerm> iterator() {
        return new SimpleTermIterator(this);
    }

    /**
     * this method returns a new Term in which
     *      all occurences of the Variable "variable" are replaced by
     *          fresh pairwise disjunct Variables
     *
     * @author Sebastian Weise
     */
    public TRSTerm linearize(TRSVariable variable) {
        return this.helpLinearize(variable, this.getVariables());
    }

    /**
     * checks that if we first rename every variable in this to a fresh variable
     * if then this newly term matches that. If this is linear this is
     * term matches that. If this is linear this is
     * matches and this.linearMatches(that) = false implies this.matches(that) =
     *
     * This method is more efficient than matches and
     *
     *
     * this.linearMatches(that) = this.matches(that) for linear terms this
     */
    public abstract boolean linearMatches(TRSTerm that);

    /**
     * checks whether <code>this</code> matches <code>that</code>,
     * i.e. whether <code>this sigma = that</code>
     * @param that
     * @return
     */
    public final boolean matches(TRSTerm that) {
        Map<TRSVariable, TRSTerm> sigma = new LinkedHashMap<TRSVariable, TRSTerm>();
        sigma = this.extendMatchingSubstitution(sigma, that);
        return sigma != null;
    }

    /**
     * all variables in the term will be renamed to new ones, where different
     * occurences of the same variables will be renamed to the same new
     * the same new variable. The generator gen is used to produce
     * @param gen
     * @return
     */
    public abstract TRSTerm renameVariables(aprove.verification.dpframework.BasicStructures.Utility.FreshVarGenerator gen);

    /**
     * all variables in the term will be renamed to new ones, where
     * different occurences of the same variables will be renamed to
     * the same new variable. It is guaranteed, that no variable
     * of vars will be present in the term afterwards.
     * @param vars
     * @return
     */
    public final TRSTerm renameVariables(Collection<TRSVariable> vars) {
        return this.renameVariables(new aprove.verification.dpframework.BasicStructures.Utility.FreshVarGenerator(vars));
    }

    public abstract TRSTerm renameVariables(Map<TRSVariable, TRSVariable> map);

    /**
     * Gets a renumbering map, a prefix, and the next free nr.
     * First, for all variables x in the term that do not occur in the keyset of the map
     * we add the assignment x/prefix_freeNr to the map and update the free nr counter accordingly.
     * Then we replace all variables in the term by their corresponding variables in the map.
     * The result is the pair of the new term and the next free nr.
     * @param map
     * @param prefix
     * @param nr
     * @return
     */
    public abstract ImmutablePair<? extends TRSTerm, Integer> renumberVariables(
        Map<TRSVariable, TRSVariable> map,
        String prefix,
        Integer nr);

    /**
     * delivers a new term where every variable is renamed to prefix_nr. The
     * numbers start with STANDARD_NUMBER and are incr. each time a new variable
     * is spotted. The term is traversed from left to right. E.g., if this =
     * f(x,y,g(x1,x),y,z) prefix = x STANDARD_NUMBER = 0 then the result will be
     * f(x0,x1,g(x2,x0),x1,x3)
     *       then the result will be f(x0,x1,g(x2,x0),x1,x3)
     * @param prefix
     * @return
     */
    public final TRSTerm renumberVariables(String prefix) {
        return this.renumberVariables(new LinkedHashMap<TRSVariable, TRSVariable>(), prefix, TRSTerm.STANDARD_NUMBER).x;
    }

    public abstract TRSTerm renameAt(Position pos, FunctionSymbol replacement);

    public abstract TRSTerm renameAtMap(Position pos, Map<FunctionSymbol, FunctionSymbol> replacements);

    public abstract TRSTerm renameAtAllMap(Set<Position> poses, Map<FunctionSymbol, FunctionSymbol> replacements);

    /**
     * delivers a new term where all occurrences of the term replace are
     * replaced by the term replacement.
     * @param replace
     * @param replacement
     * @return
     */
    public final TRSTerm replaceAll(Map<TRSTerm, TRSTerm> replaceMap) {
        if (Globals.useAssertions) {
            for (TRSTerm term : replaceMap.values()) {
                assert (term != null);
            }
        }
        return this.uncheckedReplaceAll(replaceMap);
    }

    /**
     * delivers a new term where all occurrences of the term replace are
     * replaced by the term replacement.
     * @param replace
     * @param replacement
     * @return
     */
    public final TRSTerm replaceAll(TRSTerm replace, TRSTerm replacement) {
        if (Globals.useAssertions) {
            assert (replace != null && replacement != null);
        }
        if (this.equals(replace)) {
            return replacement;
        }
        if (this.isVariable()) {
            return this;
        }
        final TRSFunctionApplication fThis = (TRSFunctionApplication) this;
        boolean changed = false;
        final ImmutableList<? extends TRSTerm> args = fThis.getArguments();
        final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(args.size());
        for (TRSTerm arg : args) {
            final TRSTerm newArg = arg.replaceAll(replace, replacement);
            if (newArg != arg) {
                changed = true;
            }
            newArgs.add(newArg);
        }
        if (changed) {
            return TRSTerm.createFunctionApplication(fThis.getRootSymbol(), newArgs);
        } else {
            return this;
        }
    }

    /**
     * @param replaceMap - maps function symbols to replacements of the
     *  same arity; symbols that are not contained in replaceMap will
     *  not be replaced
     * @return this with its function symbols replaced according to replaceMap;
     *  may or may not be a different object
     */
    public final TRSTerm replaceAllFunctionSymbols(Map<FunctionSymbol, FunctionSymbol> replaceMap) {
        if (Globals.useAssertions) {
            for (Map.Entry<FunctionSymbol, FunctionSymbol> entry : replaceMap.entrySet()) {
                assert (entry.getKey() != null && entry.getValue() != null) : "who does something like this?";
                assert (entry.getKey().getArity() == entry.getValue().getArity()) : "replacements must have same arity";
            }
        }
        return this.uncheckedReplaceAllFunctionSymbols(replaceMap);
    }

    /**
     * delivers the new term this[t]_pos. I.e., we replace the subterm of this
     * of this at position pos by t.
     * position of this.
     * @param pos - a valid position of this
     * @param t
     * @return
     */
    public final TRSTerm replaceAt(Position pos, TRSTerm t) {
        final int[] positions = pos.toIntArray();
        final int depth = positions.length;
        final FunctionSymbol[] fs = new FunctionSymbol[depth];
        final ArrayList<? extends TRSTerm>[] allArgs = new ArrayList[depth];
        TRSTerm current = this;
        int i;
        for (i = 0; i < depth; i++) {
            final TRSFunctionApplication fTerm = (TRSFunctionApplication) current;
            fs[i] = fTerm.getRootSymbol();
            final List<? extends TRSTerm> args = fTerm.getArguments();
            allArgs[i] = (ArrayList<? extends TRSTerm>) args;
            current = args.get(positions[i]);
        }
        current = t;
        while (i != 0) {
            i--;
            final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>(allArgs[i]);
            args.set(positions[i], current);
            FunctionSymbol curFs = fs[i];
            current = TRSTerm.createFunctionApplication(curFs, args);
        }
        return current;
    }

    /**
     * returns all terms which result out of all possible rewritings in R.
     * The returned set may safely be modified.
     */
    public Set<TRSTerm> rewrite(Map<FunctionSymbol, ? extends Set<Rule>> R) {
        final Set<TRSTerm> rewritings = new LinkedHashSet<TRSTerm>();
        Set<? extends Rule> usefulRules;
        for (Pair<Position, TRSTerm> actPair : this.getPositionsWithSubTerms()) {
            final TRSTerm subterm = actPair.y;
            if (subterm.isVariable()) {
                continue;
            }
            final TRSFunctionApplication fSubterm = (TRSFunctionApplication) subterm;
            if ((usefulRules = R.get(fSubterm.getRootSymbol())) == null) {
                continue;
            }
            for (Rule actRule : usefulRules) {
                final TRSFunctionApplication lhs = actRule.getLeft();
                final TRSSubstitution matcher = lhs.getMatcher(subterm);
                if (matcher != null) {
                    rewritings.add(this.replaceAt(actPair.x, actRule.getRight().applySubstitution(matcher)));
                }
            }
        }
        return rewritings;
    }

    /**
     * Returns all multi-distributions which result out of all possible rewritings in R.
     * 
     * @param term - The term we want to rewrite
     * @return Set of all possible resulting multi-distributions after a single rewrite step.
     */
    public MultiDistribution<TRSTerm> rewrite(ProbabilisticRule rule, Position p, Substitution matcher) {
        return rewriteWithProbOfTerm(rule, p, matcher, BigFraction.ONE);
    }

    /**
     * Computes the resulting multi-distribution when applying the given probabilistic rule to this term
     * at the specified position using the provided substitution.
     *
     * @param rule the probabilistic rule to apply
     * @param p the position within the term where the rule is applied
     * @param matcher the substitution that enables the rule application
     * @param probability the probability associated with the rule application
     * @return the resulting multi-distribution of terms after applying the rule once
     */

    public MultiDistribution<TRSTerm> rewriteWithProbOfTerm(ProbabilisticRule rule, Position p, Substitution matcher, BigFraction probability) {
        //final TRSTerm subterm = this.getSubterm(p);
        //final TRSFunctionApplication lhs = rule.getLeft();
        final HashMultiSet<Pair<TRSTerm, BigFraction>> resProbabilityMap = new HashMultiSet<Pair<TRSTerm, BigFraction>>();
        for (Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
            TRSTerm r = entry.getKey().getKey();
            BigFraction prob = entry.getKey().getValue();
            Integer amount = entry.getValue();
            prob = prob.multiply(probability);

            resProbabilityMap.put(new Pair<TRSTerm, BigFraction>(this.replaceAt(p, r.applySubstitution(matcher)), prob), amount);
        }
        MultiDistribution<TRSTerm> resDist = new MultiDistribution<>(resProbabilityMap);
        return resDist;
    }

    /**
     * Returns all multi-distributions which result out of all possible rewritings in R.
     * 
     * @param term - The term we want to rewrite
     * @return Set of all possible resulting multi-distributions after a single rewrite step.
     */
    public Set<MultiDistribution<? extends TRSTerm>> rewrite(Set<ProbabilisticRule> R) {
        final Set<MultiDistribution<? extends TRSTerm>> rewritings = new LinkedHashSet<MultiDistribution<? extends TRSTerm>>();

        for (ProbabilisticRule rule : R) {
            for (Pair<Position, TRSTerm> actPair : this.getPositionsWithSubTerms()) {
                final TRSTerm subterm = actPair.y;
                if (subterm.isVariable()) {
                    continue;
                }
                final TRSFunctionApplication lhs = rule.getLeft();
                final TRSSubstitution matcher = lhs.getMatcher(subterm);
                if (matcher != null) {
                    final HashMultiSet<Pair<TRSTerm, BigFraction>> resProbabilityMap = new HashMultiSet<Pair<TRSTerm, BigFraction>>();
                    for (Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
                        TRSTerm r = entry.getKey().getKey();
                        BigFraction prob = entry.getKey().getValue();
                        Integer amount = entry.getValue();

                        resProbabilityMap.put(new Pair<TRSTerm, BigFraction>(this.replaceAt(actPair.x, r.applySubstitution(matcher)), prob), amount);
                    }
                    MultiDistribution<? extends TRSTerm> resDist = new MultiDistribution<>(resProbabilityMap);
                    rewritings.add(resDist);
                }
            }
        }
        return rewritings;
    }

    /**
     * rewrites the Term as often as possible using the provided rule.
     * One better makes sure the rule to apply is terminating.
     */
    public TRSTerm rewriteAsOftenAsPossible(Rule r) {
        final TRSTerm tmpResult = this;
        for (Pair<Position, TRSTerm> actPair : tmpResult.getPositionsWithSubTerms()) {
            final TRSTerm subterm = actPair.y;
            if (subterm.isVariable()) {
                continue;
            }
            final TRSFunctionApplication lhs = r.getLeft();
            final TRSSubstitution matcher = lhs.getMatcher(subterm);
            if (matcher != null) {
                return this.replaceAt(actPair.x, r.getRight().applySubstitution(matcher)).rewriteAsOftenAsPossible(r);
            }
        }
        return tmpResult; // No more applications possible.
    }

    /**
     * returns all terms which result out of all possible rewritings in R.
     * The returned set may safely be modified.
     */
    public Set<TRSTerm> rewriteGeneralized(
        Map<FunctionSymbol, ? extends Set<? extends GeneralizedRule>> R,
        FreshNameGenerator freshNames) {
        final Set<TRSTerm> rewritings = new LinkedHashSet<TRSTerm>();
        Set<? extends GeneralizedRule> usefulRules;
        for (Pair<Position, TRSTerm> actPair : this.getPositionsWithSubTerms()) {
            final TRSTerm subterm = actPair.y;
            if (subterm.isVariable()) {
                continue;
            }
            final TRSFunctionApplication fSubterm = (TRSFunctionApplication) subterm;
            if ((usefulRules = R.get(fSubterm.getRootSymbol())) == null) {
                continue;
            }
            for (GeneralizedRule actRule : usefulRules) {
                final TRSFunctionApplication lhs = actRule.getLeft();
                TRSSubstitution matcher = lhs.getMatcher(subterm);
                if (matcher != null) {
                    if (!(actRule instanceof Rule)) {
                        final Map<TRSVariable, TRSTerm> freshVars = new LinkedHashMap<TRSVariable, TRSTerm>(matcher.toMap());
                        final int i = 0;
                        for (TRSVariable var : actRule.getRight().getVariables()) {
                            if (!freshVars.containsKey(var)) {
                                freshVars.put(var, TRSTerm.createVariable(freshNames.getFreshName("x" + i, false)));
                            }
                        }
                        matcher = TRSSubstitution.create(ImmutableCreator.create(freshVars), true);
                    }
                    rewritings.add(this.replaceAt(actPair.x, actRule.getRight().applySubstitution(matcher)));
                }
            }
        }
        return rewritings;
    }

    /**
     * checks whether this and that are semiunifiable
     * (the matcher is applied to this)
     * @param that
     * @return
     */
    public final boolean semiUnifies(TRSTerm that) {
        return new SemiUnification(this, that).semiUnify();
    }

    /**
     * checks whether this and that are semiunifiable with disjoint sets of variables
     * (the matcher is applied to this)
     * @param that
     * @return
     */
    public final boolean semiUnifiesVarDisjoint(TRSTerm that) {
        final TRSTerm thisRenamed = this.renumberVariables(TRSTerm.SECOND_STANDARD_PREFIX);
        final TRSTerm thatRenamed = that.renumberVariables(TRSTerm.THIRD_STANDARD_PREFIX);
        return thisRenamed.semiUnifies(thatRenamed);
    }

    /**
     * replaces all subterms of this with defined root symbols by pairwise
     * different fresh variables
     */
    abstract public TRSTerm tcap(ImmutableSet<FunctionSymbol> definedSymbols, FreshNameGenerator fng);

    /**
     * computes tcapR(this). If this = tcapR(this) then this is returned. (No new object creation)
     * the variables introduces by tcap are taken from SECOND_STANDARD_PREFIX.
     * It is required that the lhs of R are in STANDARD_RENUMBERED format
     * This requirements are to ensure correct unification of
     * variable disjoint terms without making all terms variable disjoint!
    
     * @param lhsR - a map from function symbols to lhs with corresponding root symbol
     */
    public final TRSTerm tcap(Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR) {
        if (Globals.useAssertions) {
            assert (TRSTerm.tcapAssertCheck(lhsR));
        }
        final ImmutablePair<TRSTerm, Integer> res = this.tcap(lhsR, TRSTerm.STANDARD_NUMBER);
        if (Globals.useAssertions) {
            assert (this == res.x || !this.equals(res.x));
        }
        return res.x;
    }

    /**
     * computes tcapE(this). The equations are given as set of AC Functionsymbols
     * Functionsymbols and C FunctionSymbols. Currently no other equations are
     * supported. If this = tcapE(this) then this is returned. (No new object
     * creation) the variables introduces by tcapE are taken from
     * SECOND_STANDARD_PREFIX. It is required that the lhs of R are in
     * STANDARD_RENUMBERED format This requirements are to ensure correct
     * unification of variable disjoint terms without making all terms variable
     * disjoint!
     * @param lhsR - a map from function symbols to lhs with corresponding root
     * symbol
     */
    public final TRSTerm tcapE(
        Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR,
        Set<FunctionSymbol> ACs,
        Set<FunctionSymbol> Cs) {
        if (Globals.useAssertions) {
            assert (TRSTerm.tcapAssertCheck(lhsR));
        }
        final ImmutablePair<TRSTerm, Integer> res = this.tcapE(lhsR, ACs, Cs, TRSTerm.STANDARD_NUMBER);
        if (Globals.useAssertions) {
            assert (this == res.x || !this.equals(res.x));
        }
        return res.x;
    }

    public Iterator<TermIterator.Entry> termPosIterator() {
        return new TermIterator(this);
    }

    @Override
    public final Element toCPF(Document doc, XMLMetaData xmlMetaData) {
        return this.toCPF2(doc, xmlMetaData);
    }

    @Override
    public final Element toDOM(Document doc, XMLMetaData xmlMetaData) {
        final Element e = XMLTag.TERM.createElement(doc);
        e.appendChild(this.toDOM2(doc, xmlMetaData));
        return e;
    }

    public abstract String toTERMPTATION(FreshNameGenerator vars, FreshNameGenerator funcs);

    /**
     * checks whether this and that are unifiable
     * @param that
     * @return
     */
    public final boolean unifies(TRSTerm that) {
        return new Unification(this, that).unify();
    }

    /**
     * checks whether this and that are rational unifiable under the condition
     * that every variable of <code>finiteVars</code> is instantiated finitely
     * @return (true, set) if the two terms unify rational under the condition that the variables of
     *                     the set must be instantiated infinitely
     *         (false, null) otherise
     */
    public final Pair<Boolean, Set<TRSVariable>> unifiesRational(TRSTerm that, Set<TRSVariable> finiteVars) {
        return new RationalUnification(this, that, finiteVars).unify();
    }

    /**
     * checks whether this and that are unifiable with disjoint sets of variables
     * @param that
     * @return
     */
    public final boolean unifiesVarDisjoint(TRSTerm that) {
        final TRSTerm thisRenamed = this.renumberVariables(TRSTerm.SECOND_STANDARD_PREFIX);
        final TRSTerm thatRenamed = that.renumberVariables(TRSTerm.THIRD_STANDARD_PREFIX);
        return thisRenamed.unifies(thatRenamed);
    }

    /**
     * Adds all leaf positions of this term to the set pts.
     * The position of the current term is given with pos.
     * @param pos
     * @param pts
     */
    protected abstract void collectLeafPositions(Position pos, Collection<Position> pts);

    /**
     * adds all positions of this term to the set pts.
     * The position of the current term is given with pos.
     * @param pos
     * @param pts
     */
    protected abstract void collectPositions(Position pos, Collection<Position> pts);

    /**
     * adds all positions and subterms of this term to the set pts.
     * The position of the current term is given with pos.
     * @param pos
     * @param pts
     * @param dropRoot - if true, then the root position will not be counted
     * @param dropVars - if true, then the variable positions will not be
     * counted
     */
    protected abstract void collectPositionsAndSubTerms(
        Position pos,
        Collection<Pair<Position, TRSTerm>> pts,
        boolean dropRoot,
        boolean dropVars);

    protected abstract void collectSubTerms(Set<TRSTerm> subs, boolean dropVars);

    /**
     * For each occurring variable, store in varPositions at which positions it
     * occurs.
     *
     * @param pos - the position of this
     * @param varPositions - stores for each occurring variable at which
     * positions it occurs in this; non-null
     */
    protected abstract void collectVariablePositions(Position pos, Map<TRSVariable, List<Position>> varPositions);

    /**
     * @param pos the /overall/ position (!) for which we want to compute the
     *  list of function symbols one sees when going to pos in this, starting
     *  from the empty position
     * @param depth the depth of this inside pos
     * @param fs the symbols we have already seen
     */
    protected abstract void computePathLabels(Position pos, int depth, List<FunctionSymbol> fs);

    protected abstract TRSTerm helpLinearize(TRSVariable variable, Set<TRSVariable> toAvoid);

    /**
     * Computes icapQRs(this). Returns this if icapQRs(this) = this (no new object). The method introduces fresh
     * variables with SECOND_STANDARD_PREFIX numbers greater than the given nr. TODO fix the rest
     * only contain variables of THIRD_STANDARD_PREFIX and that Q and lhsR are
     * non-empty. Moreover, lhsR do only contain variables of STANDARD_PREFIX!
     * It returns the pair of the new term and the next free nr.
     * @param Q
     * @param lhsR - a mapping from functionSymbols to lhss of rules with
     * corresponding root symbol
     * @param s
     * @param nr The start number for introducing fresh variables.
     * @return The result of icapQRs(this) and the next free number.
     */
    protected abstract ImmutablePair<TRSTerm, Integer> icapQRst(
        QTermSet Q,
        Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR,
        TRSFunctionApplication s,
        Integer nr);

    /**
     * Checks whether this TRSTerm is linear, does not contain variables from the specified set, and if this is true it
     * adds its own variables to the set.
     * @param alreadyPresent A set to add the variables of this to if they are not yet contained.
     * @return True if this TRSTerm is linear and does not contain variables from the specified set. False otherwise.
     */
    protected abstract boolean isLinear(Set<TRSVariable> alreadyPresent);

    /**
     * @param sigma A substitution.
     * @return The result of applying sigma to this.
     */
    protected abstract TRSTerm processSubstitution(Substitution sigma);

    /**
     * calculates tcapR(this). If tcap(this) = this we return this itself!
     * Here we introduce fresh variables with SECOND_STANDARD_PREFIX
     * and the next nr given. We return the term and the next free nr.
     * It is assumed that all lhs do only contain variables with STANDARD_PREFIX.
     * @param lhsR
     * @param nr
     * @return - a term only where all variables are from SECOND_STANDARD_PREFIX
     */
    protected abstract ImmutablePair<TRSTerm, Integer> tcap(
        Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR,
        Integer nr);

    /**
     * calculates tcapE(this). The equations are given as set of AC Functionsymbols
     * Functionsymbols and C FunctionSymbols. Currently no other equations are
     * supported. If tcapE(this) = this we return this itself! Here we introduce
     * fresh variables with SECOND_STANDARD_PREFIX and the next nr given. We
     * return the term and the next free nr. It is assumed that all lhs do only
     * contain variables with STANDARD_PREFIX.
     * @return - a term only where all variables are from SECOND_STANDARD_PREFIX
     */
    public abstract ImmutablePair<TRSTerm, Integer> tcapE(
        Map<FunctionSymbol, Set<TRSFunctionApplication>> lhsR,
        Set<FunctionSymbol> ACs,
        Set<FunctionSymbol> Cs,
        Integer nr);

    /**
     * removes the nr of occurrences of this variables from the map, if all
     * resulting values are >= 0. Then true is returned, otherwise false.
     * It is assumed that the map contains values >= 0 for all variables occurring
     * in this term
     */
    protected abstract boolean testForLessVariables(Map<TRSVariable, Integer> map);

    protected abstract Element toCPF2(Document doc, XMLMetaData xmlMetaData);

    protected abstract Element toDOM2(Document doc, XMLMetaData xmlMetaData);

    private final TRSTerm uncheckedReplaceAll(Map<TRSTerm, TRSTerm> replaceMap) {
        final TRSTerm replacement = replaceMap.get(this);
        if (replacement != null) {
            return replacement;
        }
        if (this.isVariable()) {
            return this;
        }
        final TRSFunctionApplication fThis = (TRSFunctionApplication) this;
        boolean changed = false;
        final ImmutableList<? extends TRSTerm> args = fThis.getArguments();
        final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(args.size());
        for (TRSTerm arg : args) {
            final TRSTerm newArg = arg.replaceAll(replaceMap);
            if (newArg != arg) {
                changed = true;
            }
            newArgs.add(newArg);
        }
        if (changed) {
            return TRSTerm.createFunctionApplication(fThis.getRootSymbol(), newArgs);
        } else {
            return this;
        }
    }

    private final TRSTerm uncheckedReplaceAllFunctionSymbols(Map<FunctionSymbol, FunctionSymbol> replaceMap) {
        if (this.isVariable()) {
            return this;
        }
        final TRSFunctionApplication fThis = (TRSFunctionApplication) this;
        final FunctionSymbol f = fThis.getRootSymbol();
        FunctionSymbol replacement = replaceMap.get(f);
        boolean changed;
        if (replacement == null) {
            replacement = f;
            changed = false;
        } else {
            changed = true;
        }
        final ImmutableList<? extends TRSTerm> args = fThis.getArguments();
        final ArrayList<TRSTerm> newArgs = new ArrayList<TRSTerm>(args.size());
        for (TRSTerm arg : args) {
            final TRSTerm newArg = arg.uncheckedReplaceAllFunctionSymbols(replaceMap);
            if (newArg != arg) {
                changed = true;
            }
            newArgs.add(newArg);
        }
        if (changed) {
            return TRSTerm.createFunctionApplication(replacement, newArgs);
        } else {
            return this;
        }
    }

    /**
     * Simplifies the term while keeping its semantics
     * 
     * @param term The term to simplify
     * @return Another term that has the same semantics but is possibly simpler
     */
    public TRSTerm simplify() {
        return this;
    }

    /**
     * Replace all multiplications of the form <code>c * v</code> where <code>c <= upToConstant</code>
     * by <code>v + v + ... + v</code>
     *  
     * @param upToConstant Up to which constant should constant multiplications be unfolded?
     * @return A new term that has all constant multiplications with constants smaller than the 
     * parameter unfoled to a sum
     */
    public TRSTerm unfoldConstantMultiplication(int upToConstant) {
        return this;
    }

    private static class SimpleTermIterator implements Iterator<TRSTerm> {

        private final Stack<TRSTerm> stack;

        public SimpleTermIterator(TRSTerm t) {
            this.stack = new Stack<TRSTerm>();
            this.stack.push(t);
        }

        @Override
        public boolean hasNext() {
            return !this.stack.isEmpty();
        }

        @Override
        public TRSTerm next() {
            final TRSTerm t = this.stack.pop();
            if (!t.isVariable()) {
                final TRSFunctionApplication funapp = (TRSFunctionApplication) t;
                for (TRSTerm arg : funapp.getArguments()) {
                    this.stack.push(arg);
                }
            }
            return t;
        }

        @Override
        public void remove() {
            throw new UnsupportedOperationException();
        }
    }

    // ================================================================================
    // Annotated Terms
    // ================================================================================

    /**
     * returns the set of all its annotated subterms,
     * where we removed the annotations below
     * the root of the subterms.
     * @param deAnnoMap - Maps annotated function symbols to its original ones
     * @return {#_{varepsilon}(t) | t subterm of *this*, t is annotated at the root} 
     */
    public Set<TRSFunctionApplication> subAnnoTerms(Map<FunctionSymbol, FunctionSymbol> deAnnoMap) {
        Set<TRSFunctionApplication> res = new HashSet<TRSFunctionApplication>(2);

        for (TRSFunctionApplication subterm : this.getNonVariableSubTerms()) {
            if (deAnnoMap.containsKey(subterm.getRootSymbol())) {
                Set<Position> poses = subterm.getPositions();
                poses.remove(Position.EPSILON);
                res.add(subterm.renameAtAllMap(poses, deAnnoMap));
            }
        }

        return res;
    }

    public Set<Pair<TRSFunctionApplication, Position>> getAnnoSubtermsWithPositions(Map<FunctionSymbol, FunctionSymbol> deAnnoMap) {
        Set<Pair<TRSFunctionApplication, Position>> res = new HashSet<>();

        for (Pair<Position, TRSTerm> pair : this.getPositionsWithSubTerms()) {
            if (pair.y instanceof TRSFunctionApplication fun) {
                if (deAnnoMap.containsKey(fun.getRootSymbol())) {
                    Set<Position> poses = fun.getPositions();
                    poses.remove(Position.EPSILON);
                    res.add(new Pair<>(fun.renameAtAllMap(poses, deAnnoMap), pair.x));
                }
            }
        }

        return res;
    }

    public Set<Position> getAnnoSubtermsOnlyPositions(Map<FunctionSymbol, FunctionSymbol> deAnnoMap) {
        Set<Position> res = new HashSet<>();

        for (Pair<Position, TRSTerm> pair : this.getPositionsWithSubTerms()) {
            if (pair.y instanceof TRSFunctionApplication fun) {
                if (deAnnoMap.containsKey(fun.getRootSymbol())) {
                    res.add(pair.x);
                }
            }
        }

        return res;
    }

    public abstract int countAnnos(Set<FunctionSymbol> annoSyms);

    public abstract Set<TRSFunctionApplication> getAnnoSubterms(Map<FunctionSymbol, FunctionSymbol> deAnnoMap);

    // ================================================================================
    // Term Embedding 
    // ================================================================================

    private enum occurenceProblem {
            MAXNO, MAXOO
    }

    private enum patternOccProblem {
            MAXNM, MAXOM
    }

    private int countOcc(TRSTerm that, occurenceProblem problem) {
        if (that instanceof TRSVariable || this instanceof TRSVariable) {
            return 0; // We cannot count variables and we cannot find any occurrence in a variable
        }

        var treeRepOfS = this.getTreeRep();
        var leavesOfS = treeRepOfS.getLeaves();
        Map<Position, Integer> alpha = new HashMap<>();
        Map<Position, Integer> beta = new HashMap<>();
        Map<Position, Integer> gamma = new HashMap<>();

        if (Globals.useAssertions) {
            //			assert s.getPositionsWithSubTerms() == treeRepOfS.flattenValues(): "Tree rep is not corret";
        }

        // initialize values
        for (var pair : treeRepOfS.flattenValues()) {
            alpha.put(pair.x, 0);
            beta.put(pair.x, 0);
            gamma.put(pair.x, 0);
        }
        Queue<BiTreeNode<Pair<Position, TRSTerm>>> q = new ArrayDeque<>();
        q.addAll(leavesOfS);

        while (!q.isEmpty()) {
            var sp = q.remove();
            var spPos = sp.getValue().x;
            var spTerm = sp.getValue().y;

            gamma.put(spPos, 1);
            if (sp.isLeaf()) {
                if (that.equals(spTerm)) {
                    alpha.put(spPos, 1);
                } else
                    alpha.put(spPos, 0);
            } else {
                // 1. Update Beta
                // compute positions of arguments 
                for (var arg : sp.getChildren()) {
                    var posOfArg = arg.getValue().x;
                    beta.compute(spPos, (k, v) -> v += alpha.get(posOfArg));
                }

                // 2. Update Alpha
                Integer betaSp = beta.get(spPos);
                if (that.getMatcher(spTerm) != null) { // t term occurrence s
                    List<Position> varPos = that.getVariablePositions()
                        .values()
                        .stream()
                        .flatMap(List::stream)
                        .toList();
                    Integer varPosAlphaSum = 0;
                    for (var pos : varPos) {
                        if (alpha.containsKey(spPos.append(pos))) {
                            varPosAlphaSum += alpha.get(spPos.append(pos));
                        }
                    }

                    int max;
                    switch (problem) {
                        case MAXNO -> {
                            max = Math.max(betaSp, varPosAlphaSum + 1);
                        }
                        case MAXOO -> {
                            max = Math.max(betaSp, 1);
                        }
                        default -> {
                            max = 0;
                            throw new IllegalStateException("occurenceProblem has illegal value");
                        }
                    }
                    alpha.put(spPos, max);
                } else {
                    alpha.put(spPos, betaSp);
                }

            }

            // 3. Enqueue Parents if all siblings are processed
            boolean allProccessed = true;
            if (!sp.isRoot()) {
                var siblings = sp.getParent().getChildren();
                for (var sib : siblings) {
                    var sPos = sib.getValue().x;
                    if (gamma.get(sPos) != 1) {
                        allProccessed = false;
                        break;
                    }
                }
                if (allProccessed) {
                    q.add(sp.getParent());
                }
            }
        }

        return alpha.get(Position.EPSILON);
    }

    /**
     * The maximum of two {@link OptionalInt}s, where {@link OptionalInt#empty()} represents
     * "no value" (the smallest element).
     */
    private static OptionalInt maxOpt(OptionalInt a, OptionalInt b) {
        if (a.isEmpty()) {
            return b;
        }
        if (b.isEmpty()) {
            return a;
        }
        return OptionalInt.of(Math.max(a.getAsInt(), b.getAsInt()));
    }

    /**
     * Two-state dynamic program computing {@link #maxNMSound} ({@code MAXNM}) and
     * {@link #maxOMSound} ({@code MAXOM}). For every subterm position we track
     * <ul>
     *   <li>{@code a0}: the best sum of multiplicities over any set of pairwise non-overlapping
     *       (or orthogonal) occurrences in that subterm (unconstrained; always present, &ge; 0),
     *       and</li>
     *   <li>{@code a1}: the best such sum over sets that additionally contain at least one
     *       occurrence whose closing commutes with {@code sigma} (are <em>anchored</em>). This is
     *       {@link OptionalInt#empty()} exactly when no such anchored set exists at that position.</li>
     * </ul>
     * The result is {@code a1} at the root.
     * <p>
     * The two modes differ only at an occurrence node: for {@code MAXNM} an occurrence of
     * multiplicity {@code m} may be combined with nested occurrences sitting in the variable slots
     * of {@code that}&sigma;<sup>m</sup>; for {@code MAXOM} an orthogonal occurrence excludes
     * everything strictly below it, so it contributes exactly {@code m}.
     */
    private OptionalInt countPatternOccSound(TRSTerm that, TRSSubstitution sigma, patternOccProblem problem) {
        if (this instanceof TRSVariable) {
            return OptionalInt.empty();
        }

        var treeRepOfS = this.getTreeRep();
        var leavesOfS = treeRepOfS.getLeaves();
        Map<Position, Integer> a0 = new HashMap<>();
        Map<Position, OptionalInt> a1 = new HashMap<>();
        Map<Position, Integer> gamma = new HashMap<>();

        for (var pair : treeRepOfS.flattenValues()) {
            a0.put(pair.x, 0);
            a1.put(pair.x, OptionalInt.empty());
            gamma.put(pair.x, 0);
        }
        Queue<BiTreeNode<Pair<Position, TRSTerm>>> q = new ArrayDeque<>();
        q.addAll(leavesOfS);

        while (!q.isEmpty()) {
            var sp = q.remove();
            var spPos = sp.getValue().x;
            var spTerm = sp.getValue().y;

            gamma.put(spPos, 1);

            // beta: best combination over the children (a0 sum, and a0 sum anchored by one child's a1)
            int betaA0 = 0;
            OptionalInt bestChildDelta = OptionalInt.empty(); // max over children of (a1[child] - a0[child])
            for (var arg : sp.getChildren()) {
                var posOfArg = arg.getValue().x;
                final int c0 = a0.get(posOfArg);
                final OptionalInt c1 = a1.get(posOfArg);
                betaA0 += c0;
                if (c1.isPresent()) {
                    bestChildDelta = maxOpt(bestChildDelta, OptionalInt.of(c1.getAsInt() - c0));
                }
            }
            final int betaA0Final = betaA0;
            final OptionalInt betaA1 =
                bestChildDelta.isPresent() ? OptionalInt.of(betaA0Final + bestChildDelta.getAsInt()) : OptionalInt.empty();

            if (that.getMatcher(spTerm) != null) { // there is a pattern occurrence rooted at spPos
                // find the maximal multiplicity m
                int m = 0;
                TRSTerm pumpThat = that;
                while (m <= spTerm.getSize()) {
                    TRSTerm succPump = pumpThat.applySubstitution(sigma);
                    if (succPump.getMatcher(spTerm) == null || succPump.equals(pumpThat)) {
                        break;
                    }
                    m++;
                    pumpThat = succPump;
                }
                final TRSSubstitution closing = pumpThat.getMatcher(spTerm);
                final boolean closingCommutes = closing.commutes(sigma);

                final int occA0;
                final OptionalInt occA1;
                if (problem == patternOccProblem.MAXNM) {
                    // Non-overlapping: combine this occurrence with nested occurrences that sit in
                    // the variable slots of pumpThat = that sigma^m.
                    final List<Position> varPos = pumpThat.getVariablePositions()
                        .values()
                        .stream()
                        .flatMap(List::stream)
                        .toList();
                    int varA0 = 0;
                    OptionalInt bestVarDelta = OptionalInt.empty(); // max over var slots of (a1 - a0)
                    for (var pos : varPos) {
                        final Position child = spPos.append(pos);
                        if (a0.containsKey(child)) {
                            final int c0 = a0.get(child);
                            final OptionalInt c1 = a1.get(child);
                            varA0 += c0;
                            if (c1.isPresent()) {
                                bestVarDelta = maxOpt(bestVarDelta, OptionalInt.of(c1.getAsInt() - c0));
                            }
                        }
                    }
                    occA0 = m + varA0;
                    // anchored either by this occurrence itself (if its closing commutes) or by a
                    // commuting occurrence nested in one of its variable slots.
                    if (closingCommutes) {
                        occA1 = OptionalInt.of(m + varA0);
                    } else if (bestVarDelta.isPresent()) {
                        occA1 = OptionalInt.of(m + varA0 + bestVarDelta.getAsInt());
                    } else {
                        occA1 = OptionalInt.empty();
                    }
                } else { // MAXOM
                    // Orthogonal: taking this occurrence excludes everything strictly below it, so it
                    // contributes exactly m and can only be anchored by itself.
                    occA0 = m;
                    occA1 = closingCommutes ? OptionalInt.of(m) : OptionalInt.empty();
                }

                a0.put(spPos, Math.max(betaA0, occA0));
                a1.put(spPos, maxOpt(betaA1, occA1));
            } else {
                a0.put(spPos, betaA0);
                a1.put(spPos, betaA1);
            }

            // enqueue parent once all siblings are processed
            if (!sp.isRoot()) {
                var siblings = sp.getParent().getChildren();
                boolean allProcessed = true;
                for (var sib : siblings) {
                    if (gamma.get(sib.getValue().x) != 1) {
                        allProcessed = false;
                        break;
                    }
                }
                if (allProcessed) {
                    q.add(sp.getParent());
                }
            }
        }

        return a1.get(Position.EPSILON);
    }

    /**
     * Compute maximal non-overlapping occurrences of that in this. 
     * maxNO(that, this) 
     * 
     * @param that Term for which we want to count how often it maximally occurs non-overlapping in this term 
     * @return Number of maximal non-overlapping occurrences of that in this. 
     */
    public int maxNO(TRSTerm that) {
        return countOcc(that, occurenceProblem.MAXNO);
    }

    /**
     * Compute maximal orthogonal occurrences of that in this. 
     * maxOO(that, this) 
     * 
     * @param that Term for which we want to count how often it maximally occurs orthogonally in this term.
     * @return Number of maximal orthogonal occurrences of that in this. 
     */
    public int maxOO(TRSTerm that) {
        return countOcc(that, occurenceProblem.MAXOO);
    }

    /**
     * Compute the maximal non-overlapping multiplicity of the pattern
     * <that, sigma> in this term, i.e., the maximum over all sets of pairwise
     * non-overlapping pattern occurrences that contain <em>at least one</em> occurrence whose
     * closing substitution commutes with {@code sigma}.
     *
     * @param that  base term of the pattern
     * @param sigma pumping substitution of the pattern
     * @return the maximal commutation-anchored non-overlapping multiplicity (&ge; 0), or
     *         {@link OptionalInt#empty()} if no such (anchored) set exists, i.e., the pattern does
     *         not occur with any commuting closing in this term (so this leaf may not soundly be
     *         counted non-overlapping)
     */
    public OptionalInt maxNMSound(TRSTerm that, TRSSubstitution sigma) {
        return countPatternOccSound(that, sigma, patternOccProblem.MAXNM);
    }

    /**
     * Compute the maximal orthogonal multiplicity of the pattern
     * <that, sigma> in this term, i.e., the maximum over all sets of pairwise
     * <em>orthogonal</em> pattern occurrences that contain <em>at least one</em> occurrence whose
     * closing substitution commutes with {@code sigma}.
     *
     * @param that  base term of the pattern
     * @param sigma pumping substitution of the pattern
     * @return the maximal commutation-anchored orthogonal multiplicity (&ge; 0), or
     *         {@link OptionalInt#empty()} if no such (anchored) set exists
     */
    public OptionalInt maxOMSound(TRSTerm that, TRSSubstitution sigma) {
        return countPatternOccSound(that, sigma, patternOccProblem.MAXOM);
    }

    /**
     * Returns the set of variables of x sigma, i.e., of the term that the pumping
     * substitution {@code sigma} assigns to the variable x. If x is not in the
     * domain of {@code sigma}, then x sigma = x, so the result is {x}.
     */
    private static Set<TRSVariable> varsOfImage(TRSVariable x, TRSSubstitution sigma) {
        TRSTerm image = sigma.toMap().get(x);
        if (image == null) {
            return Collections.singleton(x);
        }
        return image.getVariables();
    }

    /**
     * Checks whether the pattern term <this, sigma> is <em>linear</em>, i.e., whether
     * this sigma<sup>m</sup> is a linear term for all m.
     * <p>
     * This implements the sound and complete criterion of the dissertation of Kassing
     * (Lemma "Detecting Linear Pattern Terms (Sound and Complete)").
     *
     * @param sigma the pumping substitution of the pattern term
     * @return {@code true} iff <this, sigma> is a linear pattern term
     */
    public boolean isLinearPatternTerm(TRSSubstitution sigma) {
        // (i) t must be linear.
        if (!this.isLinear()) {
            return false;
        }

        final Set<TRSVariable> baseVars = this.getVariables();

        // (ii) x sigma must be linear for all x in dom(sigma) reachable from Vars(t) in G_{sigma, t}.
        // Compute the reachable variables by BFS over edges x -> y for y in Vars(x sigma).
        final Set<TRSVariable> reachable = new LinkedHashSet<>(baseVars);
        final Deque<TRSVariable> worklist = new ArrayDeque<>(baseVars);
        while (!worklist.isEmpty()) {
            final TRSVariable x = worklist.remove();
            for (final TRSVariable y : varsOfImage(x, sigma)) {
                if (reachable.add(y)) {
                    worklist.add(y);
                }
            }
        }
        for (final TRSVariable x : reachable) {
            final TRSTerm image = sigma.toMap().get(x);
            if (image != null && !image.isLinear()) {
                return false;
            }
        }

        // (iii) Vars(x sigma) and Vars(y sigma) must be disjoint for all concurrent pairs (x, y).
        // Compute the concurrent pairs as the fixed point of the active variable sets S_m:
        // S_0 = Vars(t), S_{m+1} = union over x in S_m of Vars(x sigma).
        final Set<Set<TRSVariable>> seen = new HashSet<>();
        final Set<Pair<TRSVariable, TRSVariable>> concurrent = new HashSet<>();
        Set<TRSVariable> active = new LinkedHashSet<>(baseVars);
        while (!active.isEmpty() && seen.add(active)) {
            final List<TRSVariable> activeList = new ArrayList<>(active);
            for (int i = 0; i < activeList.size(); i++) {
                for (int j = i + 1; j < activeList.size(); j++) {
                    concurrent.add(new Pair<>(activeList.get(i), activeList.get(j)));
                }
            }
            final Set<TRSVariable> next = new LinkedHashSet<>();
            for (final TRSVariable x : active) {
                next.addAll(varsOfImage(x, sigma));
            }
            active = next;
        }
        for (final Pair<TRSVariable, TRSVariable> pair : concurrent) {
            final Set<TRSVariable> imgX = new HashSet<>(varsOfImage(pair.x, sigma));
            imgX.retainAll(varsOfImage(pair.y, sigma));
            if (!imgX.isEmpty()) {
                return false;
            }
        }

        return true;
    }
}
