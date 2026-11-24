/**
 * @author mpluecke
 * @version $Id$
 */
package aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.IDPProblem.PfFunctions.*;
import aprove.verification.dpframework.IDPProblem.Processors.algorithms.filter.*;
import aprove.verification.dpframework.IDPProblem.Processors.nonInf.*;
import aprove.verification.dpframework.IDPProblem.utility.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.DAGNodes.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Factories.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Variables.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import immutables.*;

public class IdpCand1ShapeHeuristic implements IdpShapeHeuristic {

    protected static Logger log =
        Logger.getLogger("aprove.verification.dpframework.IDPProblem.Processors.nonInf.poly.IdpCand1ShapeHeuristic");

    protected final Map<IDPGInterpretation, Map<FunctionSymbol, Node<PosHierarchy>>> cache;
    protected final Map<Set<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>, List<GPoly<BigIntImmutable, GPolyVar>>>> maxCombiCoeffCache;
    protected final Map<ImmutablePair<FunctionSymbol, Integer>, GPoly<BigIntImmutable, GPolyVar>> linCoeffCache;

    protected final boolean lookCondNodes;
    protected final boolean maxProjectionPos;
    protected final boolean maxArithPos;
    protected final boolean normalizeConstructors;
    protected final IIDPFilterHeuristic filterHeuristic;
    private int linCoeffCounter = 0;
    private int linVarsCounter;
    private int linCoeffCacheCounter;
    private int filteredCounter;
    private int unfilteredCounter;

    @ParamsViaArgumentObject
    public IdpCand1ShapeHeuristic(final Arguments args) {
        this.cache = new LinkedHashMap<IDPGInterpretation, Map<FunctionSymbol, Node<PosHierarchy>>>();
        this.maxCombiCoeffCache =
            new LinkedHashMap<Set<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>, List<GPoly<BigIntImmutable, GPolyVar>>>>();
        this.linCoeffCache =
            new LinkedHashMap<ImmutablePair<FunctionSymbol, Integer>, GPoly<BigIntImmutable, GPolyVar>>();
        this.filterHeuristic = args.filterHeuristic;
        this.lookCondNodes = args.lookCondNodes;
        this.maxProjectionPos = args.maxProjectionPos;
        this.maxArithPos = args.maxArithPos;
        this.normalizeConstructors = args.normalizeConstructors;
    }

    @Override
    public Triple<OrderPoly<BigIntImmutable>, Map<Integer, Pair<Boolean, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>>, Map<Integer, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>> getShape(final IDPGInterpretation interpretation,
        final FunctionSymbol symbol,
        final Abortion aborter) throws AbortionException {
        final Map<FunctionSymbol, Node<PosHierarchy>> map = this.getNodeMap(interpretation);
        final Node<PosHierarchy> node = map.get(symbol);
        if (node == null) {
            // The symbol does not occur in the rules, e.g. TRUE if the IDP
            // does not use booleans. Use the default shape.
            return null;
        }
        return this.universalShape(interpretation, symbol, node.getObject(), aborter);
        /*
        if (hierarchy.maxCombiPos.isEmpty()) {
            return null;
        } else {
        }*/
    }

    @Override
    public boolean applies(final IDPGInterpretation interpretation) {
        final Map<FunctionSymbol, Node<PosHierarchy>> map = this.getNodeMap(interpretation);
        for (final Node<PosHierarchy> node : map.values()) {
            final PosHierarchy hierarchy = node.getObject();
            if (hierarchy.maxCombiPos.isEmpty()) {
                return true;
            }
        }
        return false;
    }

    private Map<FunctionSymbol, Node<PosHierarchy>> getNodeMap(final IDPGInterpretation interpretation) {
        synchronized (this.cache) {
            Map<FunctionSymbol, Node<PosHierarchy>> map = this.cache.get(interpretation);
            if (map == null) {
                this.fillCache(interpretation);
                map = this.cache.get(interpretation);
            }
            return map;
        }
    }

    // ################################################################################
    // Type Detection
    // ################################################################################
    private void fillCache(final IDPGInterpretation interpretation) {
        final Graph<PosHierarchy, List<Set<Integer>>> graph = new Graph<PosHierarchy, List<Set<Integer>>>();
        final Map<FunctionSymbol, Node<PosHierarchy>> fsMap = new LinkedHashMap<FunctionSymbol, Node<PosHierarchy>>();
        this.fillCache(graph, fsMap, interpretation.getRuleAnalysis().getRAnalysis(), interpretation);
        this.fillCache(graph, fsMap, interpretation.getRuleAnalysis().getPAnalysis(), interpretation);
        // r.println("FILTERED NOW " + filteredCounter + " vs " + unfilteredCounter);
        this.promote(graph, fsMap, interpretation);
        this.linkCondArguments(graph, fsMap, interpretation.getRuleAnalysis());
        this.cache.put(interpretation, fsMap);
    }

    private void promote(final Graph<PosHierarchy, List<Set<Integer>>> graph,
        final Map<FunctionSymbol, Node<PosHierarchy>> fsMap,
        final IDPGInterpretation interpretation) {
        // build edges
        this.buildEdges(graph, fsMap, interpretation.getRuleAnalysis().getRAnalysis(),
            interpretation.getRuleAnalysis().getPreDefinedMap());
        this.buildEdges(graph, fsMap, interpretation.getRuleAnalysis().getPAnalysis(),
            interpretation.getRuleAnalysis().getPreDefinedMap());
        this.lookAhead(graph, fsMap, interpretation.getRuleAnalysis());
        this.graphFlow(graph, fsMap);
    }

    /**
     * Pulls hierarchy along edges
     */
    private void graphFlow(final Graph<PosHierarchy, List<Set<Integer>>> graph,
        final Map<FunctionSymbol, Node<PosHierarchy>> fsMap) {
        boolean changed = false;
        do {
            changed = false;
            for (final Node<PosHierarchy> node : graph.getNodes()) {
                final Set<Edge<List<Set<Integer>>, PosHierarchy>> edges = graph.getInEdges(node);
                forEdge: for (final Edge<List<Set<Integer>>, PosHierarchy> edge : edges) {
                    final Node<PosHierarchy> from = edge.getStartNode();
                    final Node<PosHierarchy> to = edge.getEndNode();
                    if (from == to) { // no need to propagate along self-loops
                        continue forEdge;
                    }
                    final List<Set<Integer>> mapping = edge.getObject();
                    forMaxCombis: for (final Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>> maxCombi : from.getObject().maxCombiPos) {
                        final List<Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>>> mappedCombi =
                            new ArrayList<Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>>>();
                        mappedCombi.add(new LinkedHashSet<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>>());
                        final Set<Integer> mappedPos = new LinkedHashSet<Integer>();
                        for (final ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>> maxPos : maxCombi) {
                            final Set<Integer> targetPos = mapping.get(maxPos.x.intValue());
                            final int size = mappedCombi.size();
                            for (int i = 0; i < size; i++) {
                                final Iterator<Integer> targetPosIter = targetPos.iterator();
                                if (!targetPosIter.hasNext()) {
                                    continue forMaxCombis;
                                }
                                final Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>> currentCombi =
                                    mappedCombi.get(i);
                                while (targetPosIter.hasNext()) {
                                    final Integer addPos = targetPosIter.next();
                                    mappedPos.add(addPos);
                                    if (targetPosIter.hasNext()) {
                                        final Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>> add =
                                            new LinkedHashSet<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>>(
                                                currentCombi);
                                        add.add(new ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>(
                                            addPos, maxPos.y));
                                        mappedCombi.add(add);
                                    } else {
                                        currentCombi.add(new ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>(
                                            addPos, maxPos.y));
                                    }
                                }
                            }
                        }
                        if (mappedCombi.size() != 1 || mappedCombi.iterator().next().size() > 0) {
                            mappedCombi.removeAll(to.getObject().maxCombiPos);
                            if (!mappedCombi.isEmpty()) {
                                to.getObject().maxCombiPos.addAll(mappedCombi);
                                final Set<Set<Integer>> cleanedUp = to.getObject().cleanUp();
                                changed = !this.projectToPos(mappedCombi).equals(cleanedUp) || changed;
                            }
                        }
                        this.removeFromLin(to.getObject().linPos, mappedPos);
                    }
                }
            }
        } while (changed);
    }

    protected void linkCondArguments(final Graph<PosHierarchy, List<Set<Integer>>> graph,
        final Map<FunctionSymbol, Node<PosHierarchy>> fsMap,
        final IDPRuleAnalysis analysis) {
        final Map<ImmutablePair<FunctionSymbol, Integer>, ImmutablePair<Set<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<FunctionSymbol, Integer>>> equivalenceClasses =
            new LinkedHashMap<ImmutablePair<FunctionSymbol, Integer>, ImmutablePair<Set<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<FunctionSymbol, Integer>>>();
        // init equivalence classes
        for (final Node<PosHierarchy> node : graph.getNodes()) {
            for (final ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>> p : node.getObject().linPos) {
                final Set<ImmutablePair<FunctionSymbol, Integer>> cls =
                    new LinkedHashSet<ImmutablePair<FunctionSymbol, Integer>>();
                cls.add(p.y);
                equivalenceClasses.put(
                    new ImmutablePair<FunctionSymbol, Integer>(node.getObject().fsAnalysis.getFs(), p.x),
                    new ImmutablePair<Set<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<FunctionSymbol, Integer>>(
                        cls, p.y));
            }
        }

        for (final GeneralizedRule rule : analysis.getRules()) {
            if (!rule.getRight().isVariable()) {
                final TRSFunctionApplication left = rule.getLeft();
                final TRSFunctionApplication right = (TRSFunctionApplication) rule.getRight();
                final ImmutableList<TRSTerm> leftArgs = left.getArguments();
                final ImmutableList<TRSTerm> rightArgs = right.getArguments();
                for (int i = leftArgs.size() - 1; i >= 0; i--) {
                    final int index = rightArgs.indexOf(leftArgs.get(i));
                    if (index >= 0) {
                        this.linkCondArgument(right.getRootSymbol(), index,
                            new ImmutablePair<FunctionSymbol, Integer>(left.getRootSymbol(), i), fsMap,
                            equivalenceClasses, analysis);
                    } else {
                        if (Globals.DEBUG_MPLUECKER) {
                            IdpCand1ShapeHeuristic.log.finest("UNLIKABLE " + leftArgs.get(i) + "   to    " + right);
                        }
                    }
                }
            }
        }
        int linkCounter = 0;
        int unlinkCounter = 0;
        final Set<ImmutablePair<FunctionSymbol, Integer>> links =
            new LinkedHashSet<ImmutablePair<FunctionSymbol, Integer>>();
        for (final Node<PosHierarchy> node : graph.getNodes()) {
            for (final ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>> pos : node.getObject().linPos) {
                if (!pos.y.x.equals(node.getObject().fsAnalysis.getFs())) {
                    linkCounter++;
                    links.add(pos.y);
                } else {
                    unlinkCounter++;
                }
            }
        }
        IdpCand1ShapeHeuristic.log.fine("LINEAR LINKED: " + linkCounter + " vs " + unlinkCounter + " @ " + links.size());
    }

    private void linkCondArgument(final FunctionSymbol fs,
        final int pos,
        final ImmutablePair<FunctionSymbol, Integer> linkTo,
        final Map<FunctionSymbol, Node<PosHierarchy>> fsMap,
        final Map<ImmutablePair<FunctionSymbol, Integer>, ImmutablePair<Set<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<FunctionSymbol, Integer>>> equivalenceClasses,
        final IDPRuleAnalysis analysis) {
        final Node<PosHierarchy> node = fsMap.get(fs);
        final PosHierarchy hierarchy = node.getObject();
        final Iterator<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>> linIter =
            hierarchy.linPos.iterator();
        while (linIter.hasNext()) {
            final ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>> p = linIter.next();
            if (p.x == pos) {
                final ImmutablePair<Set<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<FunctionSymbol, Integer>> currentEqClass =
                    equivalenceClasses.get(p.y);
                final ImmutablePair<Set<ImmutablePair<FunctionSymbol, Integer>>, ImmutablePair<FunctionSymbol, Integer>> linkedEqClass =
                    equivalenceClasses.get(linkTo);
                if (currentEqClass != linkedEqClass && linkedEqClass != null) {
                    if (Globals.DEBUG_MPLUECKER) {
                        IdpCand1ShapeHeuristic.log.finest("LINK " + fs + "/" + pos + "   to    " + linkTo.x + "/" + linkTo.y);
                    }
                    linkedEqClass.x.addAll(currentEqClass.x);
                    for (final ImmutablePair<FunctionSymbol, Integer> cEq : currentEqClass.x) {
                        final PosHierarchy cEqHierarchy = fsMap.get(cEq.x).getObject();
                        final Iterator<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>> cEqlinIter =
                            cEqHierarchy.linPos.iterator();
                        while (linIter.hasNext()) {
                            final ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>> cEqP =
                                cEqlinIter.next();
                            if (cEqP.x == cEq.y) {
                                cEqlinIter.remove();
                                cEqHierarchy.linPos.add(new ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>(
                                    cEqP.x, linkedEqClass.y));
                                break;
                            }
                        }
                        equivalenceClasses.put(cEq, linkedEqClass);
                    }
                    /*
                    linIter.remove();
                    if (!p.y.x.equals(fs) || p.y.y != pos) {
                        linkCondArgument(p.y.x, p.y.y, linkTo, fsMap, equivalenceClasses, analysis);
                    }
                    hierarchy.linPos.add(new ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>(pos, linkTo));
                    Collection<GeneralizedRule> rules = analysis.getRuleMap().get(fs);
                    if (rules != null) {
                        for (GeneralizedRule rule : rules) {
                            if (!rule.getRight().isVariable()) {
                                FunctionApplication left = rule.getLeft();
                                FunctionApplication right = (FunctionApplication) rule.getRight();
                                ImmutableArrayList<Term> leftArgs = left.getArguments();
                                ImmutableArrayList<Term> rightArgs = right.getArguments();
                                int index = rightArgs.indexOf(leftArgs.get(pos));
                                if (index >= 0) {
                                    linkCondArgument(right.getRootSymbol(), index, new ImmutablePair<FunctionSymbol, Integer>(left.getRootSymbol(), pos), fsMap, equivalenceClasses, analysis);
                                } else {
                                    if (Globals.DEBUG_MPLUECKER) {
                                        log.finest("UNLIKABLE " + leftArgs.get(pos) + "   to    " + right);
                                    }
                                }
                            }
                        }
                    }*/
                }
                return;
            }
        }
        if (Globals.DEBUG_MPLUECKER) {
            IdpCand1ShapeHeuristic.log.finest("LINK AT FILTERED POSITION " + fs + "/" + pos);
        }
    }

    private void buildEdges(final Graph<PosHierarchy, List<Set<Integer>>> graph,
        final Map<FunctionSymbol, Node<PosHierarchy>> fsMap,
        final RuleAnalysis<GeneralizedRule> analysis,
        final IDPPredefinedMap predefinedMap) {
        final Map<FunctionSymbol, ImmutableSet<GeneralizedRule>> ruleMap = analysis.getRuleMap();
        for (final Map.Entry<FunctionSymbol, ImmutableSet<GeneralizedRule>> fsEntry : ruleMap.entrySet()) {
            final FunctionSymbol fs = fsEntry.getKey();
            final int arity = fs.getArity();
            final ImmutableSet<GeneralizedRule> rules = fsEntry.getValue();
            final Node<PosHierarchy> node = fsMap.get(fs);
            for (final GeneralizedRule rule : rules) {
                if (!rule.getRight().isVariable()) {
                    final TRSFunctionApplication faR = (TRSFunctionApplication) rule.getRight();
                    // compute var positions
                    final Set<TRSVariable> rVariables = rule.getRight().getVariables();
                    final Map<TRSVariable, List<Integer>> rVarPos = new LinkedHashMap<TRSVariable, List<Integer>>();
                    {
                        final ArrayList<Set<TRSVariable>> posToVar = new ArrayList<Set<TRSVariable>>(arity);
                        for (final TRSTerm rArg : faR.getArguments()) {
                            if (PredefinedUtil.onlyPredefinedArithmetic(rArg, predefinedMap)) {
                                posToVar.add(rArg.getVariables());
                            } else {
                                posToVar.add(Collections.<TRSVariable>emptySet());
                            }
                        }
                        for (final TRSVariable var : rVariables) {
                            final List<Integer> positions = new ArrayList<Integer>(arity);
                            for (int i = faR.getRootSymbol().getArity() - 1; i >= 0; i--) {
                                if (posToVar.get(i).contains(var)) {
                                    positions.add(i);
                                }
                            }
                            rVarPos.put(var, positions);
                        }
                    }

                    Edge<List<Set<Integer>>, PosHierarchy> edge = graph.getEdge(node, fsMap.get(faR.getRootSymbol()));
                    if (edge == null) {
                        final List<Set<Integer>> posMapping = new ArrayList<Set<Integer>>(fs.getArity());
                        for (int i = fs.getArity() - 1; i >= 0; i--) {
                            posMapping.add(new LinkedHashSet<Integer>());
                        }
                        edge =
                            new Edge<List<Set<Integer>>, PosHierarchy>(node, fsMap.get(faR.getRootSymbol()), posMapping);
                        graph.addEdge(edge);
                    }
                    final List<Set<Integer>> posMapping = edge.getObject();

                    for (int i = arity - 1; i >= 0; i--) {
                        final Set<TRSVariable> argVars = rule.getLeft().getArgument(i).getVariables();
                        final Set<Integer> dependentR = posMapping.get(i);
                        for (final TRSVariable var : argVars) {
                            final List<Integer> rVarPositions = rVarPos.get(var);
                            if (rVarPositions != null) {
                                for (final Integer rVarPosition : rVarPositions) {
                                    dependentR.add(rVarPosition);
                                }
                            }
                        }
                    }
                }
            }
        }
    }

    protected Set<TRSTerm> getMaxArithHeads(final TRSTerm term, final IDPPredefinedMap predefinedMap) {
        if (term.isVariable()) {
            return java.util.Collections.emptySet();
        } else {
            final TRSFunctionApplication fa = (TRSFunctionApplication) term;
            final FunctionSymbol fs = fa.getRootSymbol();
            if (predefinedMap.isPredefined(fs)) {
                return java.util.Collections.emptySet();
            }
            final Set<TRSTerm> res = new LinkedHashSet<TRSTerm>();
            for (final TRSTerm arg : fa.getArguments()) {
                if (!arg.isVariable()) {
                    if (predefinedMap.isPredefined(((TRSFunctionApplication) arg).getRootSymbol())) {
                        res.add(term);
                    }
                    res.addAll(this.getMaxArithHeads(arg, predefinedMap));
                } else {
                    res.add(term);
                }
            }
            return res;
        }
    }

    private void fillCache(final Graph<PosHierarchy, List<Set<Integer>>> graph,
        final Map<FunctionSymbol, Node<PosHierarchy>> fsMap,
        final RuleAnalysis<GeneralizedRule> analysis,
        final IDPGInterpretation interpretation) {
        for (final FunctionSymbol symbol : analysis.getFunctionSymbols()) {
            final Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>> lin =
                new LinkedHashSet<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>>();
            final Collection<Integer> filteredPositions =
                this.filterHeuristic.getFilteredPositions(interpretation.getRuleAnalysis(), symbol);
            for (int i = symbol.getArity() - 1; i >= 0; i--) {
                if (!filteredPositions.contains(i)) {
                    lin.add(new ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>(i,
                        new ImmutablePair<FunctionSymbol, Integer>(symbol, i)));
                    this.unfilteredCounter++;
                } else {
                    this.filteredCounter++;
                }
            }
            final FunctionAnalysis fsAna = analysis.getFunctionAnalysis(symbol);
            final Set<Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>>> maxCombi =
                new LinkedHashSet<Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>>>();
            if (this.maxProjectionPos) {
                final ImmutableSet<Integer> projectionPos = fsAna.getProjectionPos();
                if (!projectionPos.isEmpty()) {
                    final Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>> combi =
                        new LinkedHashSet<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>>();
                    for (final Integer pos : projectionPos) {
                        if (!filteredPositions.contains(pos)) {
                            combi.add(new ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>(pos,
                                new ImmutablePair<FunctionSymbol, Integer>(symbol, pos)));
                        }
                    }
                    if (!combi.isEmpty()) {
                        maxCombi.add(combi);
                    }
                    this.removeFromLin(lin, projectionPos);
                }
            }
            // abs
            final PosHierarchy hierarchy = new PosHierarchy(lin, maxCombi, fsAna);
            if (this.maxArithPos) {
                this.evaluateDependencies(fsAna.getDependencies(), symbol, hierarchy);
            }
            final Node<PosHierarchy> node = new Node<PosHierarchy>(hierarchy);
            graph.addNode(node);
            fsMap.put(symbol, node);
        }
    }

    protected void removeFromLin(final Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>> lin,
        final Collection<Integer> pos) {
        final Iterator<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>> linIter = lin.iterator();
        while (linIter.hasNext()) {
            final ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>> p = linIter.next();
            if (pos.contains(p.x)) {
                linIter.remove();
            }
        }
    }

    protected void removeFromLin(final Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>> lin,
        final Integer pos) {
        final Iterator<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>> linIter = lin.iterator();
        while (linIter.hasNext()) {
            final ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>> p = linIter.next();
            if (pos.equals(p.x)) {
                linIter.remove();
            }
        }
    }

    protected void evaluateDependencies(final Map<Integer, RelDependency> dependencies,
        final FunctionSymbol symbol,
        final PosHierarchy hierarchy) {
        for (final Map.Entry<Integer, RelDependency> dep1 : dependencies.entrySet()) {
            final Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>> combi =
                new LinkedHashSet<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>>();
            if (dep1.getValue() == RelDependency.Wild) {
                combi.add(new ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>(dep1.getKey(),
                    new ImmutablePair<FunctionSymbol, Integer>(symbol, dep1.getKey())));
                this.removeFromLin(hierarchy.linPos, dep1.getKey());
            }
            for (final Map.Entry<Integer, RelDependency> dep2 : dependencies.entrySet()) {
                if (dep1 != dep2 && dep2.getValue() != RelDependency.Wild) {
                    if (this.depIntersect(dep1.getValue(), dep2.getValue())) {
                        if (combi.add(new ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>(dep1.getKey(),
                            new ImmutablePair<FunctionSymbol, Integer>(symbol, dep1.getKey())))) {
                            this.removeFromLin(hierarchy.linPos, dep1.getKey());
                        }
                        combi.add(new ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>(dep2.getKey(),
                            new ImmutablePair<FunctionSymbol, Integer>(symbol, dep2.getKey())));
                        this.removeFromLin(hierarchy.linPos, dep2.getKey());
                    }
                }
            }
            if (combi.size() <= 3) {
                hierarchy.maxCombiPos.add(combi);
            }
        }
        hierarchy.cleanUp();
    }

    protected boolean depIntersect(final RelDependency d1, final RelDependency d2) {
        return (d1 == RelDependency.Wild && d2 != RelDependency.Independent)
            || (d2 == RelDependency.Wild && d1 != RelDependency.Independent)
            || (d1 == d2 && d1 != RelDependency.Independent);
    }

    public Set<Set<Integer>> projectToPos(final Collection<Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>>> maxCombiPos) {
        final Set<Set<Integer>> projection = new LinkedHashSet<Set<Integer>>();
        for (final Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>> maxCombi : maxCombiPos) {
            final Set<Integer> usedPos = new LinkedHashSet<Integer>();
            for (final ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>> pos : maxCombi) {
                usedPos.add(pos.x);
            }
            projection.add(usedPos);
        }
        return projection;
    }

    // ################################################################################
    // Poly Creation
    // ################################################################################
    /**
     * @param linearVars a*x_1
     * @param absVars for entry e : (2s-1)max(a * x_{e.x}, b * x_{e.x}} where a = 1, b = -1 iff e.y = false
     * @param maxCombinations for entry e: (2s-1)max(a * x_{e.x} + b * x_{e.y}, c * x_{e.x} + d * x_{e.y}}
     * @return x: poly shape
     *         y: side constraints
     *         z: vfi-map
     */
    protected Triple<OrderPoly<BigIntImmutable>, Map<Integer, Pair<Boolean, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>>, Map<Integer, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>> universalShape(final IDPGInterpretation interpretation,
        final FunctionSymbol symbol,
        final PosHierarchy hierarchy,
        final Abortion aborter) throws AbortionException {
        // build coeffs + v_f_i

        final int arity = symbol.getArity();
        final OrderPolyFactory<BigIntImmutable> factory = interpretation.getFactory();
        final GPolyFactory<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> polyFactory = factory.getFactory();
        final GPolyFactory<BigIntImmutable, GPolyVar> innerFactory = factory.getInnerFactory();
        final Vector<GPoly<BigIntImmutable, GPolyVar>> linearCoeffs =
            new Vector<GPoly<BigIntImmutable, GPolyVar>>(arity);
        linearCoeffs.setSize(arity);
        final ArrayList<VarPartNode<GPolyVar>> variables = new ArrayList<VarPartNode<GPolyVar>>(arity);
        final Vector<List<GPoly<BigIntImmutable, GPolyVar>>> vfi_constraints =
            new Vector<List<GPoly<BigIntImmutable, GPolyVar>>>();
        for (int i = 0; i < arity; i++) {
            final GPolyVar var = interpretation.getVariableForFunctionSymbolArgument(i);
            variables.add(polyFactory.buildVariable(var));
            vfi_constraints.add(new ArrayList<GPoly<BigIntImmutable, GPolyVar>>());
        }
        aborter.checkAbortion();

        Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>> linearVars;

        if (interpretation.isTupleNat()
            || (interpretation.isNat() && !interpretation.getRuleAnalysis().getPAnalysis().getRootSymbols().contains(
                symbol))) {
            linearVars =
                new LinkedHashSet<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>>(hierarchy.linPos);
            final Iterator<Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>>> maxCombiIter =
                hierarchy.maxCombiPos.iterator();
            while (maxCombiIter.hasNext()) {
                aborter.checkAbortion();
                final Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>> combi = maxCombiIter.next();
                if (combi.size() == 1) {
                    final int pos = combi.iterator().next().x;
                    linearVars.add(new ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>(pos,
                        new ImmutablePair<FunctionSymbol, Integer>(symbol, pos)));
                    maxCombiIter.remove();
                }
            }
        } else {
            linearVars = hierarchy.linPos;
        }
        final boolean isConstrToNormalize =
            this.normalizeConstructors && interpretation.getRuleAnalysis().isConstructor(symbol)
                && linearVars.size() == 1;
        GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> res;
        if (isConstrToNormalize) {
            res = null;
        } else {
            res = factory.buildFromCoeff(interpretation.getNextCoeffPoly(symbol));
        }

        synchronized (this.linCoeffCache) {
            // linear parts
            this.linVarsCounter += linearVars.size();
            for (final ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>> i : linearVars) {
                aborter.checkAbortion();
                GPoly<BigIntImmutable, GPolyVar> coeff;
                if (isConstrToNormalize) {
                    coeff = innerFactory.one();
                } else {
                    coeff = this.linCoeffCache.get(i.y);
                    if (coeff == null) {
                        coeff = interpretation.getNextCoeffPoly(symbol);
                        this.linCoeffCounter++;
                        this.linCoeffCache.put(i.y, coeff);
                    } else {
                        this.linCoeffCacheCounter++;
                    }
                }
                linearCoeffs.set(i.x, coeff);
                final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> linearPart =
                    polyFactory.concat(coeff, variables.get(i.x));
                if (res != null) {
                    res = polyFactory.plus(res, linearPart);
                } else {
                    res = linearPart;
                }
                vfi_constraints.get(i.x).add(coeff);
            }
            if (Globals.DEBUG_MPLUECKER) {
                IdpCand1ShapeHeuristic.log.fine("LINEAR COEFFS " + this.linCoeffCounter + " vs " + this.linCoeffCacheCounter + " / "
                    + this.linVarsCounter);
            }
        }

        synchronized (this.maxCombiCoeffCache) {
            // maxParts
            for (final Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>> maxCombi : hierarchy.maxCombiPos) {
                aborter.checkAbortion();
                if (maxCombi.isEmpty()) {
                    continue;
                }
                final Set<ImmutablePair<FunctionSymbol, Integer>> origin =
                    new LinkedHashSet<ImmutablePair<FunctionSymbol, Integer>>(maxCombi.size());
                FunctionSymbol origSymbol = null;
                for (final ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>> pos : maxCombi) {
                    if (origSymbol == null) {
                        origSymbol = pos.y.x;
                    } else {
                        if (Globals.useAssertions) {
                            assert (origSymbol == pos.y.x);
                        }
                    }
                    origin.add(pos.y);
                }
                ImmutablePair<GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>, List<GPoly<BigIntImmutable, GPolyVar>>> max_addToVfi =
                    this.maxCombiCoeffCache.get(origin);
                if (max_addToVfi == null) {
                    final List<GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>> maxArgs =
                        new ArrayList<GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>(origin.size());
                    for (int i = origin.size() - 1; i >= 0; i--) {
                        maxArgs.add(polyFactory.zero());
                    }
                    final VarPartNode<GPolyVar> maxSwitchVar =
                        innerFactory.buildVariable(interpretation.getNextCoeff(interpretation.getBoolRange()));
                    final GPoly<BigIntImmutable, GPolyVar> outerSwitch =
                        innerFactory.minus(factory.getInnerFactory().concat(BigIntImmutable.TWO, maxSwitchVar),
                            factory.getInnerFactory().one());
                    int argPos = 0;
                    final Vector<GPoly<BigIntImmutable, GPolyVar>> addToVfi =
                        new Vector<GPoly<BigIntImmutable, GPolyVar>>(origSymbol.getArity());
                    addToVfi.setSize(origSymbol.getArity());
                    for (final ImmutablePair<FunctionSymbol, Integer> pos : origin) {
                        aborter.checkAbortion();
                        final VarPartNode<GPolyVar> var =
                            polyFactory.buildVariable(interpretation.getVariableForFunctionSymbolArgument(pos.y));
                        if (origin.size() <= 2) {
                            for (int i = origin.size() - 1; i >= 0; i--) {
                                final GPoly<BigIntImmutable, GPolyVar> coeff =
                                    interpretation.getNextCoeffPoly(origSymbol);
                                maxArgs.set(i, polyFactory.plus(maxArgs.get(i), polyFactory.concat(coeff, var)));
                                if (addToVfi.get(pos.y) != null) {
                                    addToVfi.set(pos.y, innerFactory.plus(addToVfi.get(pos.y), coeff));
                                } else {
                                    addToVfi.set(pos.y, coeff);
                                }
                            }
                        } else {
                            final GPoly<BigIntImmutable, GPolyVar> coeff = interpretation.getNextCoeffPoly(origSymbol);
                            maxArgs.set(argPos, polyFactory.concat(coeff, var));
                            addToVfi.set(pos.y, coeff);
                        }
                        argPos++;
                    }
                    final GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> max =
                        polyFactory.times(polyFactory.buildFromCoeff(outerSwitch), polyFactory.max(maxArgs));
                    max_addToVfi =
                        new ImmutablePair<GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>, List<GPoly<BigIntImmutable, GPolyVar>>>(
                            max, addToVfi);
                    for (int i = origSymbol.getArity() - 1; i >= 0; i--) {
                        aborter.checkAbortion();
                        if (addToVfi.get(i) != null) {
                            addToVfi.set(i, innerFactory.times(outerSwitch, addToVfi.get(i)));
                        }
                    }
                    this.maxCombiCoeffCache.put(origin, max_addToVfi);
                }

                final Map<GPolyVar, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>> subst =
                    new LinkedHashMap<GPolyVar, GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar>>();
                for (final ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>> maxPos : maxCombi) {
                    aborter.checkAbortion();
                    if (max_addToVfi.y.get(maxPos.y.y) != null) {
                        vfi_constraints.get(maxPos.x).add(max_addToVfi.y.get(maxPos.y.y));
                    }
                    if (maxPos.y.y.intValue() != maxPos.x.intValue()) {
                        subst.put(interpretation.getVariableForFunctionSymbolArgument(maxPos.y.y),
                            factory.concat(innerFactory.one(), variables.get(maxPos.x)));
                    }
                }
                GPoly<GPoly<BigIntImmutable, GPolyVar>, GPolyVar> maxPart;
                if (subst.isEmpty()) {
                    maxPart = max_addToVfi.x;
                } else {
                    maxPart = polyFactory.substituteVariables(max_addToVfi.x, subst, null, aborter);
                }
                if (res != null) {
                    res = polyFactory.plus(res, maxPart);
                } else {
                    res = maxPart;
                }
            }
        }
        if (res != null) {
            final Map<Integer, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>> vfiMap =
                new LinkedHashMap<Integer, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>();
            final Map<Integer, Pair<Boolean, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>> sideConstraints =
                new LinkedHashMap<Integer, Pair<Boolean, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>>();
            final ConstraintFactory<BigIntImmutable> constraintFactory = interpretation.getConstraintFactory();
            final OrderPolyConstraint<BigIntImmutable> TRUE = constraintFactory.createTrue();
            for (int i = arity - 1; i >= 0; i--) {
                aborter.checkAbortion();
                if (vfi_constraints.isEmpty()) {
                    vfiMap.put(i,
                        new ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>(
                            TRUE, TRUE));
                } else {
                    OrderPolyConstraint<BigIntImmutable> vfi_inc = interpretation.createVFILogVar(symbol, i, true);
                    OrderPolyConstraint<BigIntImmutable> vfi_dec = interpretation.createVFILogVar(symbol, i, false);
                    final List<GPoly<BigIntImmutable, GPolyVar>> constraints = vfi_constraints.get(i);
                    final Set<OrderPolyConstraint<BigIntImmutable>> incConstraints =
                        new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
                    final Set<OrderPolyConstraint<BigIntImmutable>> decConstraints =
                        new LinkedHashSet<OrderPolyConstraint<BigIntImmutable>>();
                    for (final GPoly<BigIntImmutable, GPolyVar> constraint : constraints) {
                        final Pair<GPoly<BigIntImmutable, GPolyVar>, GPoly<BigIntImmutable, GPolyVar>> sorted =
                            SortNatPoly.sort(interpretation, constraint);
                        final OrderPoly<BigIntImmutable> x = factory.buildFromCoeff(sorted.x);
                        final OrderPoly<BigIntImmutable> y = factory.buildFromCoeff(sorted.y);
                        incConstraints.add(constraintFactory.createWithQuantifier(x, y, ConstraintType.GE));
                        decConstraints.add(constraintFactory.createWithQuantifier(y, x, ConstraintType.GE));
                    }
                    OrderPolyConstraint<BigIntImmutable> incConstraint;
                    if (incConstraints.isEmpty()) {
                        vfi_inc = incConstraint = constraintFactory.createTrue();
                    } else {
                        incConstraint =
                            constraintFactory.createOr(constraintFactory.createNot(vfi_inc),
                                constraintFactory.createAnd(incConstraints));
                    }
                    OrderPolyConstraint<BigIntImmutable> decConstraint;
                    if (incConstraints.isEmpty()) {
                        vfi_dec = decConstraint = constraintFactory.createTrue();
                    } else {
                        decConstraint =
                            constraintFactory.createOr(constraintFactory.createNot(vfi_dec),
                                constraintFactory.createAnd(decConstraints));
                    }
                    sideConstraints.put(
                        i,
                        new Pair<Boolean, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>(
                            false,
                            new ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>(
                                incConstraint, decConstraint)));
                    vfiMap.put(i,
                        new ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>(
                            vfi_inc, vfi_dec));
                }
            }
            return new Triple<OrderPoly<BigIntImmutable>, Map<Integer, Pair<Boolean, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>>, Map<Integer, ImmutablePair<OrderPolyConstraint<BigIntImmutable>, OrderPolyConstraint<BigIntImmutable>>>>(
                factory.wrap(res), sideConstraints, vfiMap);
        } else {
            return null;
        }
    }

    protected void lookAhead(final Graph<PosHierarchy, List<Set<Integer>>> graph,
        final Map<FunctionSymbol, Node<PosHierarchy>> fsMap,
        final IDPRuleAnalysis ruleAnalysis) {
        if (!this.lookCondNodes) {
            return;
        }
        final Map<FunctionSymbol, ImmutableSet<GeneralizedRule>> ruleMap =
            new LinkedHashMap<FunctionSymbol, ImmutableSet<GeneralizedRule>>(ruleAnalysis.getRAnalysis().getRuleMap());
        ruleMap.putAll(ruleAnalysis.getPAnalysis().getRuleMap());
        for (final Map.Entry<FunctionSymbol, Node<PosHierarchy>> entry : fsMap.entrySet()) {
            final FunctionSymbol fs = entry.getKey();
            final Map<Integer, RelDependency> dependencies =
                new LinkedHashMap<Integer, RelDependency>(entry.getValue().getObject().fsAnalysis.getDependencies());
            if (ruleMap.containsKey(fs)) {
                for (final GeneralizedRule rule : ruleMap.get(fs)) {
                    if (!rule.getRight().isVariable() && Utils.isCondRule(rule, ruleAnalysis.getPreDefinedMap())) {
                        final TRSFunctionApplication right = (TRSFunctionApplication) rule.getRight();
                        final Node<PosHierarchy> toNode = fsMap.get(right.getRootSymbol());
                        final Edge<List<Set<Integer>>, PosHierarchy> edge = graph.getEdge(entry.getValue(), toNode);
                        final List<Set<Integer>> posMapping = edge.getObject();
                        final Map<Integer, RelDependency> toDependencies =
                            toNode.getObject().fsAnalysis.getDependencies();
                        for (int i = fs.getArity() - 1; i >= 0; i--) {
                            RelDependency dependency = dependencies.get(i);
                            for (final Integer pos : posMapping.get(i)) {
                                dependency = this.addDependency(dependency, toDependencies.get(pos));
                            }
                            if (dependency != null) {
                                dependencies.put(i, dependency);
                            }
                        }
                        if (this.maxArithPos) {
                            this.evaluateDependencies(dependencies, fs, entry.getValue().getObject());
                        }
                    }
                }
            }
        }
    }

    protected RelDependency addDependency(final RelDependency current, final RelDependency add) {
        if (current == null) {
            return add;
        } else if (add == null) {
            return current;
        } else if (current == RelDependency.Wild || add == RelDependency.Wild) {
            return RelDependency.Wild;
        } else if (current == RelDependency.Independent) {
            return add;
        } else if (add == RelDependency.Independent) {
            return current;
        } else if (current != add) {
            return RelDependency.Wild;
        } else {
            return current;
        }
    }

    protected static class PosHierarchy {
        public final Set<Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>>> maxCombiPos;
        public final Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>> linPos;
        public final FunctionAnalysis fsAnalysis;

        public PosHierarchy(final Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>> linPos,
                final Set<Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>>> maxCombiPos,
                final FunctionAnalysis fsAnalysis) {
            this.maxCombiPos = maxCombiPos;
            this.linPos = linPos;
            this.fsAnalysis = fsAnalysis;
        }

        public Set<Set<Integer>> cleanUp() {
            final Map<Set<Integer>, Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>>> usedCombis =
                new LinkedHashMap<Set<Integer>, Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>>>();
            final Set<Set<Integer>> removed = new LinkedHashSet<Set<Integer>>();
            for (Set<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>> maxCombi : this.maxCombiPos) {
                final Set<Integer> usedPos = new LinkedHashSet<Integer>();
                for (final ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>> pos : maxCombi) {
                    usedPos.add(pos.x);
                }
                if (usedCombis.containsKey(usedPos)) {
                    removed.add(usedPos);
                    maxCombi = new LinkedHashSet<ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>>();
                    final FunctionSymbol fs = this.fsAnalysis.getFs();
                    for (final Integer pos : usedPos) {
                        maxCombi.add(new ImmutablePair<Integer, ImmutablePair<FunctionSymbol, Integer>>(pos,
                            new ImmutablePair<FunctionSymbol, Integer>(fs, pos)));
                    }
                } else {
                    usedCombis.put(usedPos, maxCombi);
                }
            }
            this.maxCombiPos.clear();
            this.maxCombiPos.addAll(usedCombis.values());
            return removed;
        }

    }

    public static class Arguments {
        public IIDPFilterHeuristic filterHeuristic = new IdpCand1FilterHeuristic();
        public boolean lookCondNodes = true;
        public boolean maxProjectionPos = true;
        public boolean maxArithPos = true;
        public boolean normalizeConstructors = true;
    }
}
