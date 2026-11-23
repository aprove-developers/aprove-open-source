package aprove.verification.probabilistic.Termination.ADPProblem;

import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;

import aprove.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.ADPProblem.AST.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import immutables.*;

/**
 * Same as @see aprove.verification.probabilistic.ADPProblem.ProbQDependencyGraph
 * but computes every edge instead of just looking at the SCCs.
 * This is needed for complexity analysis.
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class ProbQComplexityDependencyGraph implements Immutable {

    // ================================================================================
    // Properties
    // ================================================================================

    private final Graph<ProbabilisticRule, ?> g;
    private final ProbQUsableRules capCalculator; // the method to obtain capped terms (can be reused later!)
    // this component contains the TRS R and Q!

    private final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap;

    private final ADP_AST_TransformationInfo transformationInfo; // values for heuristics of NRI-transformations.

    /* computed values */
    private final QTermSet Q;
    private final boolean QsuperR;

    //Map to store the usable terms for each DT, DTs stored in STD representation
    private Map<ProbabilisticRule, Set<TRSFunctionApplication>> dtToUsableTerms;

    //Map to store the successor DTs for each usable term and the corresponding connection substititution.
    //First Sub is the ordinary connection substitution and the second one is the star connection substitution.
    //Note that the capped term uses variables of 2. and 3. Prefix (first renamed to 3.Prefix and then introduce 2.Prefix vars)
    //DTs stored in STD representation.
    private Map<TRSFunctionApplication, Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>>> usableTermsToSuccessorWithMGU;
    //TODO: Make both of the above final

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    /**
     * create Graph from scratch, if P is given, or start with "graph", if graph is given.
     * @param P - a set of DPs
     * @param graph a graph over DPs
     * @param sWithQ
     */
    private ProbQComplexityDependencyGraph(final Set<ProbabilisticRule> P,
        final PQTRSProblem sWithQ,
        final Graph<ProbabilisticRule, ?> graph,
        final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        if (Globals.useAssertions) {
            assert ((P == null) == (graph != null)); // exactly one of graph and P must be given
        }
        this.Q = sWithQ.getQ();
        this.annoMap = annoMap;
        this.capCalculator = sWithQ.getProbQUsableRulesCalculator(annoMap);
        this.QsuperR = sWithQ.QsupersetOfLhsR();
        final Set<FunctionSymbol> defsOfR = sWithQ.getDefSymbolsOfR();
        if (graph == null) {
            final int n = P.size();
            final Set<Node<ProbabilisticRule>> nodes = new LinkedHashSet<>(n);
            for (final ProbabilisticRule dp : P) {
                nodes.add(new Node<>(dp));
            }
            this.g = new Graph<>(nodes);
            this.transformationInfo = new ADP_AST_TransformationInfo(nodes);

            // iterate through all possible edges
            Node<ProbabilisticRule>[] nodeArr = new Node[n];
            nodeArr = nodes.toArray(nodeArr);

            // first do crude approximation on root symbols
            // (this check requires non-collapsing rules!)
            for (int i = 0; i < n; i++) {
                final Node<ProbabilisticRule> fromDP = nodeArr[i];
                final ProbabilisticRule fromDPRule = fromDP.getObject();
                for (int j = i + 1; j < n; j++) {
                    final Node<ProbabilisticRule> toDP = nodeArr[j];
                    final ProbabilisticRule toDPRule = toDP.getObject();
                    // standard direction
                    if (calculateFastConnection(fromDPRule, toDPRule, defsOfR)) {
                        this.g.addEdge(fromDP, toDP);
                    }
                    // reverse direction
                    if (calculateFastConnection(toDPRule, fromDPRule, defsOfR)) {
                        this.g.addEdge(toDP, fromDP);
                    }
                }
                // and self-cycle
                if (calculateFastConnection(fromDPRule, fromDPRule, defsOfR)) {
                    this.g.addEdge(fromDP, fromDP);
                }
            }
        } else {
            // we have a given graph, but of course we have to check whether we can
            // delete additional edges
            this.transformationInfo = new ADP_AST_TransformationInfo(graph.getNodes());
            this.g = graph;
            final Set<Pair<Node<ProbabilisticRule>, Node<ProbabilisticRule>>> delete = new LinkedHashSet<>();
            for (final Edge<?, ProbabilisticRule> edge : this.g.getEdges()) {
                final Node<ProbabilisticRule> start = edge.getStartNode();
                final Node<ProbabilisticRule> end = edge.getEndNode();
                if (!calculateFastConnection(start.getObject(), end.getObject(), defsOfR)) {
                    delete.add(new Pair<>(start, end));
                }
            }
            // now update graph
            for (final Pair<Node<ProbabilisticRule>, Node<ProbabilisticRule>> edge : delete) {
                this.g.removeEdge(edge.x, edge.y);
            }
        }

        final Pair<Map<TRSFunctionApplication, Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>>>, Map<ProbabilisticRule, Set<TRSFunctionApplication>>> usableTermsMaps =
            refineEdges();
        this.usableTermsToSuccessorWithMGU = usableTermsMaps.x;
        this.dtToUsableTerms = usableTermsMaps.y;
    }

    /**
     * create graph where P is a subset of the nodes in superGraph
     * => we do not have to check edges again
     * @param P
     * @param superGraph
     */
    private ProbQComplexityDependencyGraph(final Set<Node<ProbabilisticRule>> P, final ProbQComplexityDependencyGraph superGraph) {
        if (Globals.useAssertions) {
            assert (superGraph.g.getNodes().containsAll(P));
        }
        this.transformationInfo = superGraph.transformationInfo.getSubInfo(P);
        this.capCalculator = superGraph.capCalculator;
        this.g = superGraph.g.getSubGraph(P);
        this.Q = superGraph.Q;
        this.QsuperR = superGraph.QsuperR;
        this.annoMap = superGraph.annoMap;

        //TODO: We do not need to compute this here again, as P is already fully evaluated
        final Pair<Map<TRSFunctionApplication, Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>>>, Map<ProbabilisticRule, Set<TRSFunctionApplication>>> usableTermsMaps =
            refineEdges();
        this.usableTermsToSuccessorWithMGU = usableTermsMaps.x;
        this.dtToUsableTerms = usableTermsMaps.y;
    }

    /**
     * creates a DP-Graph from a given (fully evaluated graph) P and
     * the super DP-graph which contains the underlying TRS.
     * This constructor is intended for DP-transformations.
     * @param P
     * @param superGraph
     */
    private ProbQComplexityDependencyGraph(final Graph<ProbabilisticRule, ?> P,
        final ADP_AST_TransformationInfo transformationInfo,
        final ProbQComplexityDependencyGraph superGraph,
        final Set<ProbabilisticRule> newRules) {
        this.transformationInfo = transformationInfo;
        this.annoMap = superGraph.annoMap;

        final PQTRSProblem oldPQTRS = superGraph.capCalculator.getUnderlyingPQTRS();
        final Set<ProbabilisticRule> newPR = new HashSet<>();
        newPR.addAll(oldPQTRS.getPR());
        newPR.addAll(newRules);
        final PQTRSProblem newPQTRS =
            PQTRSProblem.create(ImmutableCreator.create(newPR), oldPQTRS.getQ(), oldPQTRS.getStrat(), oldPQTRS.getTarget(), oldPQTRS.isBasic());
        this.capCalculator = newPQTRS.getProbQUsableRulesCalculator(this.annoMap);

        this.g = P;
        this.Q = superGraph.Q;
        this.QsuperR = superGraph.QsuperR;

        //TODO: We do not need to compute this here again, as P is already fully evaluated
        final Pair<Map<TRSFunctionApplication, Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>>>, Map<ProbabilisticRule, Set<TRSFunctionApplication>>> usableTermsMaps =
            refineEdges();
        this.usableTermsToSuccessorWithMGU = usableTermsMaps.x;
        this.dtToUsableTerms = usableTermsMaps.y;
    }

    /**
     * creates a DP-Graph from a given DP-graph superGraph
     * and a collection of edges that should be dropped in the new graph.
     * @param P
     * @param superGraph
     */
    private ProbQComplexityDependencyGraph(
        final Collection<Pair<Node<ProbabilisticRule>, Node<ProbabilisticRule>>> dropTheseEdges,
        final ProbQComplexityDependencyGraph superGraph) {
        this.transformationInfo = superGraph.transformationInfo;
        this.capCalculator = superGraph.capCalculator;
        this.g = superGraph.g.getCopy();
        this.Q = superGraph.Q;
        this.QsuperR = superGraph.QsuperR;
        this.annoMap = superGraph.annoMap;

        // now delete edges
        for (final Pair<Node<ProbabilisticRule>, Node<ProbabilisticRule>> edge : dropTheseEdges) {
            final Node<ProbabilisticRule> from = edge.x;
            final Node<ProbabilisticRule> to = edge.y;
            this.g.removeEdge(from, to);
        }

        final Pair<Map<TRSFunctionApplication, Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>>>, Map<ProbabilisticRule, Set<TRSFunctionApplication>>> usableTermsMaps =
            refineEdges();
        this.usableTermsToSuccessorWithMGU = usableTermsMaps.x;
        this.dtToUsableTerms = usableTermsMaps.y;
    }

    /**
     * create graph where P is a subset of the nodes in superGraph and
     * the edges are guaranteed to be included in the superGraph,
     * i.e. only existent edges may be deleted.
     * @param P
     * @param superGraph
     */
    private ProbQComplexityDependencyGraph(final Set<Node<ProbabilisticRule>> P,
        final PQTRSProblem sWithQ,
        final ProbQComplexityDependencyGraph superGraph) {
        if (Globals.useAssertions) {
            assert (superGraph.g.getNodes().containsAll(P));
        }
        this.transformationInfo = superGraph.transformationInfo.getSubInfo(P);
        this.annoMap = superGraph.annoMap;
        this.capCalculator = sWithQ.getProbQUsableRulesCalculator(this.annoMap);
        this.Q = sWithQ.getQ();
        this.QsuperR = sWithQ.QsupersetOfLhsR();

        // create graph with corresponding node-set
        this.g = superGraph.g.getSubGraph(P);

        final Pair<Map<TRSFunctionApplication, Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>>>, Map<ProbabilisticRule, Set<TRSFunctionApplication>>> usableTermsMaps =
            refineEdges();
        this.usableTermsToSuccessorWithMGU = usableTermsMaps.x;
        this.dtToUsableTerms = usableTermsMaps.y;
    }

    /**
     * create a new PQRTSProblem where rWithQ are the usable rules and the supProblem satisfies QsuperR.
     * Then the edges in the graph remain identical.
     * @param sWithQ
     * @param superGraph
     */
    private ProbQComplexityDependencyGraph(final PQTRSProblem sWithQ, final ProbQComplexityDependencyGraph superGraph) {
        assert (superGraph.QsuperR);
        this.transformationInfo = superGraph.transformationInfo;
        this.annoMap = superGraph.annoMap;
        this.capCalculator = sWithQ.getProbQUsableRulesCalculator(this.annoMap);
        this.Q = sWithQ.getQ();
        this.QsuperR = sWithQ.QsupersetOfLhsR();

        // create graph with corresponding node-set
        final Graph<ProbabilisticRule, ?> supGraph = superGraph.g;
        this.g = supGraph.getSubGraph(supGraph.getNodes());

        final Pair<Map<TRSFunctionApplication, Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>>>, Map<ProbabilisticRule, Set<TRSFunctionApplication>>> usableTermsMaps =
            refineEdges();
        this.usableTermsToSuccessorWithMGU = usableTermsMaps.x;
        this.dtToUsableTerms = usableTermsMaps.y;
        //TODO: Check why this was not needed in the nonprob setting
    }

    private ProbQComplexityDependencyGraph(final PQTRSProblem sWithQ,
        final Graph<ProbabilisticRule, Object> dpGraph,
        final ProbQComplexityDependencyGraph oldGraph) {

        this.annoMap = oldGraph.annoMap;
        this.capCalculator = sWithQ.getProbQUsableRulesCalculator(this.annoMap);
        this.g = dpGraph;
        this.Q = sWithQ.getQ();
        this.QsuperR = oldGraph.QsuperR;

        //TODO change this!
        this.transformationInfo = new ADP_AST_TransformationInfo(dpGraph.getNodes());

        final Pair<Map<TRSFunctionApplication, Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>>>, Map<ProbabilisticRule, Set<TRSFunctionApplication>>> usableTermsMaps =
            refineEdges();
        this.usableTermsToSuccessorWithMGU = usableTermsMaps.x;
        this.dtToUsableTerms = usableTermsMaps.y;
    }

    public ProbQComplexityDependencyGraph(final Graph<ProbabilisticRule, ?> P,
        final ADP_AST_TransformationInfo transformationInfo,
        final ProbQComplexityDependencyGraph superGraph,
        final Map<ProbabilisticRule, Set<TRSFunctionApplication>> dtToUsableTerms2,
        final Map<TRSFunctionApplication, Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>>> usableTermsToSuccessorsWithMGU) {

        this.transformationInfo = transformationInfo;
        this.capCalculator = superGraph.capCalculator;
        this.g = P;
        this.Q = superGraph.Q;
        this.QsuperR = superGraph.QsuperR;
        this.annoMap = superGraph.annoMap;

        //TODO: We do not need to compute this here again, as P is already fully evaluated
        final Pair<Map<TRSFunctionApplication, Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>>>, Map<ProbabilisticRule, Set<TRSFunctionApplication>>> usableTermsMaps =
            refineEdges();
        this.usableTermsToSuccessorWithMGU = usableTermsMaps.x;
        this.dtToUsableTerms = usableTermsMaps.y;
    }

    /**
     * @param P note that the graph does not have to be the DP-graph but can be arbitary. However, the graph
     * will be modified when it is detected that one can delete some more edges!
     * @param rWithQ
     * @return
     */
    public static ProbQComplexityDependencyGraph
        create(final Graph<ProbabilisticRule, ?> P, final PQTRSProblem sWithQ, final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        return new ProbQComplexityDependencyGraph(null, sWithQ, P, annoMap);
    }

    /**
     * @param P
     * @param rWithQ
     * @return
     */
    public static ProbQComplexityDependencyGraph
        create(final Set<ProbabilisticRule> P, final PQTRSProblem sWithQ, final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        return new ProbQComplexityDependencyGraph(P, sWithQ, null, annoMap);
    }

    // ================================================================================
    // Accessors
    // ================================================================================

    public ImmutableSet<ProbabilisticRule> getP() {
        return ImmutableCreator.create(this.g.getNodeObjects());
    }

    /**
     * returns the internal graph. This graph must not be modified,
     * but may only be used for lookup-reasons.
     */
    public Graph<ProbabilisticRule, ?> getGraph() {
        return this.g;
    }

    public Map<TRSFunctionApplication, Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>>> getUsablePairsMap() {
        return this.usableTermsToSuccessorWithMGU;
    }

    /**
     * returns the transformation Info. This info provides information
     * for the heuristics for the DP-Transformations Narrowing, R.,I.,FI.
     */
    public ADP_AST_TransformationInfo getTransformationInfo() {
        return this.transformationInfo;
    }

    /**
     * creates a new DP-graph from this one by dropping a set of edges.
     * @param dropTheseEdges
     * @return
     */
    public ProbQComplexityDependencyGraph getSubGraphByDroppingEdges(
        final Collection<Pair<Node<ProbabilisticRule>, Node<ProbabilisticRule>>> dropTheseEdges) {
        return new ProbQComplexityDependencyGraph(dropTheseEdges, this);
    }

    public ProbQComplexityDependencyGraph getSubGraph(final Set<Node<ProbabilisticRule>> P) {
        return new ProbQComplexityDependencyGraph(P, this);
    }

    public ProbQComplexityDependencyGraph getSubGraphFromPRules(final Set<ProbabilisticRule> P) {
        final Set<Node<ProbabilisticRule>> nodesForP = this.g.getNodesFromObjects(P);
        return new ProbQComplexityDependencyGraph(nodesForP, this);
    }

    /**
     * creates a graph where P is a subset of the nodes and we draw edges
     * according to a new rWithQ
     */
    public ProbQComplexityDependencyGraph getSubGraph(final Set<ProbabilisticRule> P, final PQTRSProblem sWithQ) {
        final Set<Node<ProbabilisticRule>> nodesForP = this.g.getNodesFromObjects(P);
        return new ProbQComplexityDependencyGraph(nodesForP, sWithQ, this);
    }

    /**
     * returns the graph where we restrict R to the usableRules.
     * Here, this problem has to be innermost.
     * @param sWithQ
     * @return
     */
    public ProbQComplexityDependencyGraph getUsableRulesSubGraph(final PQTRSProblem sWithQ) {
        return new ProbQComplexityDependencyGraph(sWithQ, this);
    }

    /**
     * returns the usable rules of a DP,
     * only available in innermost case
     * @param s_to_t
     */
    public Set<ProbabilisticRule> getUsableRules(final ProbabilisticRule s_to_t) {
        return this.capCalculator.getUsableRules(s_to_t);
    }

    /**
     * returns the leaf rules of a DP graph
     * @param s_to_t
     */
    public Set<ProbabilisticRule> getLeafRules() {
        final Set<ProbabilisticRule> leafRules = new HashSet<>();
        final Set<Node<ProbabilisticRule>> nodes = getGraph().getNodes();

        for (final Node<ProbabilisticRule> n : nodes) {
            final Set<Node<ProbabilisticRule>> nodes_out = getGraph().getOut(n);
            if (nodes_out.isEmpty()) {
                leafRules.add(n.getObject());
            }
        }
        return leafRules;
    }

    /**
     * checks whether there are any unusable Pairs
     * @return
     */
    public boolean doUnusablePairsExist() {

        for (final Node<ProbabilisticRule> node : this.g.getNodes()) {
            final ProbabilisticRule depTuple = node.getObject();
            for (final TRSFunctionApplication t : depTuple.getAllAnnoSubterms(this.annoMap.getRLMap())) {
                if (isUnusableTerm(t)) {
                    return true;
                }
            }
        }

        return false;
    }

    /**
     * checks whether the given Term is unusable
     * @return
     */
    public boolean isUnusableTerm(final TRSFunctionApplication t) {
        final TRSFunctionApplication tSTD = (TRSFunctionApplication) t.getStandardRenumbered();
        if (!this.usableTermsToSuccessorWithMGU.containsKey(tSTD) || this.usableTermsToSuccessorWithMGU.get(tSTD).isEmpty()) {
            return true;
        }
        return false;
    }

    /**
     * Returns the graph when we replace s_to_t by the newDPs and add the new rules.
     * The transformation and position p is only needed to update
     * the transformation info for the heuristics.
     * Moreover, the new counter for the given transformation of the newDPs is returned
     *
     * Does not create the usable terms mappings! This is done by the constructor at the end.
     *
     * @param transformation
     * @param s_to_t
     * @param newDPs
     * @param newRules
     * @param p
     * @return Pair of new graph and the new counter for the given transformation of the newDPs
     */
    public Pair<ProbQComplexityDependencyGraph, Integer>
        getTransformedGraph(final ADP_AST_Transformation transformation,
            final Node<ProbabilisticRule> s_to_t,
            final Set<ProbabilisticRule> newDPs,
            final Set<ProbabilisticRule> newRules,
            final Position p) {
        final Graph<ProbabilisticRule, ?> newGraph = this.g.getCopy();
        final Node<ProbabilisticRule>[] newNodes = new Node[newDPs.size()];
        int i = 0;
        for (final ProbabilisticRule newDP : newDPs) {
            final Node<ProbabilisticRule> newNode = new Node<>(newDP);
            newNodes[i] = newNode;
            newGraph.addNode(newNode);
            i++;
        }

        final boolean noStar = !this.QsuperR && this.capCalculator.getUnderlyingPQTRS().isCollapsing();

        // incoming edges
        for (final Node<ProbabilisticRule> prev : newGraph.getIn(s_to_t)) {
            if (!prev.equals(s_to_t)) {
                final ProbabilisticRule prevDT = prev.getObject();
                for (final Node<ProbabilisticRule> newDTNode : newNodes) {
                    final ProbabilisticRule newDT = newDTNode.getObject();
                    final Set<Pair<TRSFunctionApplication, TRSSubstitution>> connectionSet = calculateConnectionWithUsableTerms(prevDT, newDT);
                    if (!connectionSet.isEmpty()) {
                        // the star check is only applicable if Q is a superset of R or if the PQTRS is non-collapsing
                        if (noStar || !calculateStarConnectionWithUsableTerms(prevDT, newDT).isEmpty()) {
                            //Add new Edge
                            newGraph.addEdge(prev, newDTNode);
                        }
                    }
                }
            }
        }

        // outgoing edges
        for (final Node<ProbabilisticRule> next : newGraph.getOut(s_to_t)) {
            if (!next.equals(s_to_t)) {
                final ProbabilisticRule nextDT = next.getObject();
                for (final Node<ProbabilisticRule> newDTNode : newNodes) {
                    final ProbabilisticRule newDT = newDTNode.getObject();

                    final Set<Pair<TRSFunctionApplication, TRSSubstitution>> connectionSet = calculateConnectionWithUsableTerms(newDT, nextDT);
                    if (!connectionSet.isEmpty()) {

                        // the star check is only applicable if Q is a superset of R or if the PQTRS is non-collapsing
                        if (noStar || !calculateStarConnectionWithUsableTerms(newDT, nextDT).isEmpty()) {
                            //Add new Edge
                            newGraph.addEdge(newDTNode, next);
                        }
                    }
                }
            }
        }

        // self loop
        if (newGraph.contains(s_to_t, s_to_t)) {
            for (final Node<ProbabilisticRule> newDTNode : newNodes) {
                final ProbabilisticRule newDT = newDTNode.getObject();
                for (final Node<ProbabilisticRule> otherNew : newNodes) {
                    final ProbabilisticRule otherNewDT = otherNew.getObject();

                    final Set<Pair<TRSFunctionApplication, TRSSubstitution>> connectionSet = calculateConnectionWithUsableTerms(newDT, otherNewDT);
                    if (!connectionSet.isEmpty()) {

                        // the star check is only applicable if Q is a superset of R or if the PQTRS is non-collapsing
                        if (noStar || !calculateStarConnectionWithUsableTerms(newDT, otherNewDT).isEmpty()) {
                            //Add new Edge
                            newGraph.addEdge(newDTNode, otherNew);
                        }
                    }
                }
            }
        }

        // delete s_to_t
        newGraph.removeNode(s_to_t);

        // delete identical nodes (inserted rule with same connections already present)
        final Set<Node<ProbabilisticRule>> reallyNewNodes = new HashSet<>(newNodes.length);
        dp: for (final Node<ProbabilisticRule> newDP : newNodes) {
            final Set<Node<ProbabilisticRule>> possiblySame = newGraph.getAllNodesFromObject(newDP.getObject());
            if (possiblySame.size() > 1) {
                final Set<Node<ProbabilisticRule>> out = newGraph.getOut(newDP);
                final Set<Node<ProbabilisticRule>> in = newGraph.getIn(newDP);
                for (final Node<ProbabilisticRule> oldNode : possiblySame) {
                    if (!oldNode.equals(newDP)) {
                        // if same incoming and outgoing connections, then we delete the newDP
                        if (newGraph.getOut(oldNode).equals(out) && newGraph.getIn(oldNode).equals(in)) {
                            newGraph.removeNode(newDP);
                            continue dp;
                        }
                    }
                }
            }
            reallyNewNodes.add(newDP);
        }

        final Pair<ADP_AST_TransformationInfo, Integer> transInfoCounter = this.transformationInfo.getTransformedInfo(transformation, s_to_t, reallyNewNodes, p);

        return new Pair<>(new ProbQComplexityDependencyGraph(newGraph, transInfoCounter.x, this, newRules),
            transInfoCounter.y);
    }

    // ================================================================================
    // Internals
    // ================================================================================

    /**
     * only checks on outermost symbols
     * @param from
     * @param to
     * @param defSymsOfR - the defined symbols of R.
     * @return false, if there is no edge
     */
    private boolean calculateFastConnection(final ProbabilisticRule from,
        final ProbabilisticRule to,
        final Set<FunctionSymbol> defSymsOfR) {

        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : from.getRight().getProbabilityMapping().entrySet()) {
            final TRSTerm rhsTerm = entry.getKey().getKey();

            for (final Pair<TRSFunctionApplication, Position> termPosPair : rhsTerm.getAnnoSubtermsWithPositions(this.annoMap.getRLMap())) {
                final TRSFunctionApplication term = termPosPair.x;
                final FunctionSymbol f = term.getRootSymbol();
                final FunctionSymbol g = to.getRootSymbol();
                if (f.equals(g) || defSymsOfR.contains(f)) {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Does the usual forward checks with T/ICap.
     * Additionally, we compute the terms that can lead to the rule "to" (Usable Terms)
     * and the corresponding substitutions. The Sub
     * @param from
     * @param to
     * @return Set of pairs of usable terms and corresponding connection substitution.
     */
    private Set<Pair<TRSFunctionApplication, TRSSubstitution>> calculateConnectionWithUsableTerms(final ProbabilisticRule from,
        final ProbabilisticRule to) {

        final Set<Pair<TRSFunctionApplication, TRSSubstitution>> usableTermsWithMGUSet = new HashSet<>();

        final Set<Pair<TRSFunctionApplication, TRSFunctionApplication>> capped_s_to_t = this.capCalculator.getCappedDP(from);

        for (final Pair<TRSFunctionApplication, TRSFunctionApplication> pair : capped_s_to_t) {

            final TRSFunctionApplication u = to.getLhsInStandardRepresentation();

            final TRSFunctionApplication cappedTerm = pair.x;
            final TRSFunctionApplication normalTerm = pair.y;

            final TRSSubstitution sigma = cappedTerm.getMGU(u);

            if (sigma == null) {
                continue;
            } else if (!this.Q.isEmpty()) {
                // no normal form conditions in Q = empty case

                // check normal form condition u sigma
                final TRSTerm u_sigma = u.applySubstitution(sigma);
                if (this.Q.canBeRewritten(u_sigma)) {
                    continue;
                } else {

                    final TRSTerm s = from.getLeft();

                    // check normal form condition s sigma
                    final TRSTerm s_sigma = this.QsuperR ? s.applySubstitution(sigma) : s;
                    // s = s sigma in termination case
                    if (this.Q.canBeRewritten(s_sigma)) {
                        continue;
                    } else {
                        usableTermsWithMGUSet.add(new Pair<>(normalTerm, sigma));
                    }
                }
            } else {
                usableTermsWithMGUSet.add(new Pair<>(normalTerm, sigma));
            }
        }
        return usableTermsWithMGUSet;
    }

    /**
     * Does the star check. Either Q super R has to be true or the TRS must be non-collapsing.
     * Additionally, we compute the terms that can lead to the rule "to" (Usable Terms).
     * @param from
     * @param to
     * @return false, if edge can be deleted;
     */
    private Set<Pair<TRSFunctionApplication, TRSSubstitution>> calculateStarConnectionWithUsableTerms(final ProbabilisticRule from,
        final ProbabilisticRule to) {
        final Set<Pair<TRSFunctionApplication, TRSSubstitution>> usableTermsWithMGUSet = new HashSet<>();

        final TRSTerm cap_u;

        if (this.QsuperR) {
            cap_u = this.capCalculator.getCapUsedRminusOneOfU(from, to);
        } else {
            if (Globals.useAssertions) {
                assert (!this.capCalculator.getUnderlyingPQTRS().isCollapsing());
            }
            cap_u = this.capCalculator.getCapRminusOneOfU(to);
        }

        final MultiDistribution<TRSTerm> distRHS = from.getRhsInStandardRepresentation();

        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : distRHS.getProbabilityMapping().entrySet()) {
            final TRSTerm rhsTerm = entry.getKey().getKey();

            for (final Pair<TRSFunctionApplication, Position> termPosPair : rhsTerm.getAnnoSubtermsWithPositions(this.annoMap.getRLMap())) {

                final TRSFunctionApplication term = termPosPair.x;

                final TRSSubstitution sigma = term.getMGU(cap_u);

                if (sigma == null) {
                    continue;
                } else if (!cap_u.isVariable() && !this.Q.isEmpty()) {
                    // do some Q-normal checks (if cap_u is variable, then we do not change anything, and s in Q-NF has been checked before

                    final TRSTerm sSigma = from.getLhsInStandardRepresentation().applySubstitution(sigma);
                    if (this.Q.canBeRewritten(sSigma)) {
                        continue;
                    } else {
                        usableTermsWithMGUSet.add(new Pair<>(term, sigma));
                    }
                } else {
                    usableTermsWithMGUSet.add(new Pair<>(term, sigma));
                }
            }
        }
        return usableTermsWithMGUSet;
    }

    /**
     * Computes a finer connection on edges and compute the usablePairs
     */
    private
        Pair<Map<TRSFunctionApplication, Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>>>, Map<ProbabilisticRule, Set<TRSFunctionApplication>>>
        refineEdges() {

        final List<Edge<?, ProbabilisticRule>> edges = new ArrayList<>(this.g.getEdges());

        Map<ProbabilisticRule, Set<TRSFunctionApplication>> dtToUsableTerms = new HashMap<>();
        //Init the sets for all DTs in the graph for the dtToUsableTerms map
        for (final Node<ProbabilisticRule> node : this.g.getNodes()) {
            final Set<TRSFunctionApplication> usableTermsForDT = new HashSet<>();
            dtToUsableTerms.put(node.getObject().getStandardRepresentation(), usableTermsForDT);
        }

        Map<TRSFunctionApplication, Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>>> usableTermsToSuccessors = new HashMap<>();

        for (final Edge<?, ProbabilisticRule> e : edges) {
            final Node<ProbabilisticRule> from = e.getStartNode();
            final Node<ProbabilisticRule> to = e.getEndNode();
            final Set<Pair<TRSFunctionApplication, TRSSubstitution>> connectionSet = calculateConnectionWithUsableTerms(from.getObject(),
                to.getObject());
            if (connectionSet.isEmpty()) {
                this.g.removeEdge(from, to);
            } else {
                //Update the dtToUsableTerms map
                final Set<TRSFunctionApplication> usableForDT = dtToUsableTerms.get(from.getObject().getStandardRepresentation());
                for (final Pair<TRSFunctionApplication, TRSSubstitution> pair : connectionSet) {
                    usableForDT.add((TRSFunctionApplication) pair.x.getStandardRenumbered());
                }
                dtToUsableTerms.put(from.getObject().getStandardRepresentation(), usableForDT);

                //Update the usableTermsToSuccessors map
                for (final Pair<TRSFunctionApplication, TRSSubstitution> pair : connectionSet) {
                    final TRSFunctionApplication tSTD = (TRSFunctionApplication) pair.x.getStandardRenumbered();
                    if (usableTermsToSuccessors.containsKey(tSTD)) {
                        final Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>> usableForSet = usableTermsToSuccessors.get(tSTD);
                        usableForSet.add(new Triple<>(to.getObject().getStandardRepresentation(), pair.y, null));
                        usableTermsToSuccessors.put(tSTD, usableForSet);
                    } else {
                        final Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>> usableForSet = new HashSet<>();
                        usableForSet.add(new Triple<>(to.getObject().getStandardRepresentation(), pair.y, null));
                        usableTermsToSuccessors.put(tSTD, usableForSet);
                    }
                }
            }
        }

        // now check *-graph conditions
        final PQTRSProblem qtrs = this.capCalculator.getUnderlyingPQTRS();
        if (this.QsuperR || !qtrs.isCollapsing()) {

            final Map<ProbabilisticRule, Set<TRSFunctionApplication>> dtToUsableTermsStar = new HashMap<>();
            //Init the sets for all DTs in the graph for the dtToUsableTerms map
            for (final Node<ProbabilisticRule> node : this.g.getNodes()) {
                final Set<TRSFunctionApplication> usableTermsForDT = new HashSet<>();
                dtToUsableTermsStar.put(node.getObject().getStandardRepresentation(), usableTermsForDT);
            }

            final Map<TRSFunctionApplication, Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>>> usableTermsToSuccessorsStar = new HashMap<>();

            for (final Edge<?, ProbabilisticRule> e : edges) {
                final Node<ProbabilisticRule> from = e.getStartNode();
                final Node<ProbabilisticRule> to = e.getEndNode();
                final Set<Pair<TRSFunctionApplication, TRSSubstitution>> connectionSet = calculateStarConnectionWithUsableTerms(from.getObject(),
                    to.getObject());
                if (connectionSet.isEmpty()) {
                    this.g.removeEdge(from, to);
                } else {
                    //Update the dtToUsableTerms map
                    final Set<TRSFunctionApplication> usableForDT = dtToUsableTermsStar.get(from.getObject().getStandardRepresentation());
                    for (final Pair<TRSFunctionApplication, TRSSubstitution> pair : connectionSet) {
                        usableForDT.add((TRSFunctionApplication) pair.x.getStandardRenumbered());
                    }
                    dtToUsableTermsStar.put(from.getObject().getStandardRepresentation(), usableForDT);

                    //Update the usableTermsToSuccessors map
                    for (final Pair<TRSFunctionApplication, TRSSubstitution> pair : connectionSet) {
                        final TRSFunctionApplication tSTD = (TRSFunctionApplication) pair.x.getStandardRenumbered();
                        if (usableTermsToSuccessorsStar.containsKey(tSTD)) {
                            final Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>> usableForSet = usableTermsToSuccessorsStar.get(tSTD);
                            usableForSet.add(new Triple<>(to.getObject().getStandardRepresentation(), null, pair.y));
                            usableTermsToSuccessorsStar.put(tSTD, usableForSet);
                        } else {
                            final Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>> usableForSet = new HashSet<>();
                            usableForSet.add(new Triple<>(to.getObject().getStandardRepresentation(), null, pair.y));
                            usableTermsToSuccessorsStar.put(tSTD, usableForSet);
                        }
                    }
                }
            }

            // Take the intersection of both usablePairsMaps
            final Map<ProbabilisticRule, Set<TRSFunctionApplication>> dtToUsableTermsIntersection = new HashMap<>();
            for (final Entry<ProbabilisticRule, Set<TRSFunctionApplication>> entry : dtToUsableTerms.entrySet()) {
                final ProbabilisticRule dtSTD = entry.getKey();
                final Set<TRSFunctionApplication> set = entry.getValue();

                if (dtToUsableTermsStar.containsKey(dtSTD)) {
                    final Set<TRSFunctionApplication> usableForDT = dtToUsableTermsStar.get(dtSTD);
                    usableForDT.retainAll(set);
                    dtToUsableTermsIntersection.put(dtSTD, usableForDT);
                }
            }
            dtToUsableTerms = dtToUsableTermsIntersection;

            final Map<TRSFunctionApplication, Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>>> usableTermsToSuccessorIntersection = new HashMap<>();
            for (final Entry<TRSFunctionApplication, Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>>> entry : usableTermsToSuccessors.entrySet()) {
                final TRSFunctionApplication tSTD = entry.getKey();
                final Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>> set = entry.getValue();

                if (usableTermsToSuccessorsStar.containsKey(tSTD)) {
                    final Set<Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution>> finalSet = new HashSet<>();
                    for (final Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution> firstTriple : set) {

                        for (final Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution> starTriple : usableTermsToSuccessorsStar.get(tSTD)) {
                            if (firstTriple.x.equals(starTriple.x)) {
                                finalSet.add(new Triple<>(firstTriple.x, firstTriple.y, starTriple.z));
                            }
                        }
                    }
                    usableTermsToSuccessorIntersection.put(tSTD, finalSet);
                }
            }
            usableTermsToSuccessors = usableTermsToSuccessorIntersection;
        }

        return new Pair<>(usableTermsToSuccessors, dtToUsableTerms);
    }

    /**
     * Returns all possible substitution when unifying cap_u(v) with s for some v in the dist of the first dt.
     * Here s is taken with 1. prefix var and u_to_v with 3. prefix var. Fresh vars from cap have 2. prefix.
     * Note that the connection between these nodes must be present in this graph.
     * (This implies that also Q-normal checks have been performed already!)
     * Otherwise the result may be anything including null.
     * @param s_to_t
     * @param u_to_v
     */
    public Set<TRSSubstitution> getConnectingSubstitutions(final Node<ProbabilisticRule> from, final Node<ProbabilisticRule> to) {
        final Set<TRSSubstitution> allSubs = new HashSet<>();

        for (final TRSFunctionApplication usableTerm : this.dtToUsableTerms.get(from.getObject().getStandardRepresentation())) {
            for (final Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution> successorTriple : this.usableTermsToSuccessorWithMGU.get(usableTerm)) {
                if (successorTriple.x.equals(to.getObject().getStandardRepresentation())) {
                    allSubs.add(successorTriple.y);
                }
            }
        }

        return allSubs;
    }

    /**
     * Returns all possible substitution when unifying cap_R^-1(u) with t for some t in the dist of the first dt.
     * Here t is taken with 1. prefix var and u_to_v with 3. prefix var. Fresh vars from cap have 2. prefix.
     * Note that the connection between these nodes must be present in this graph.
     * (This implies that also Q-normal checks have been performed already!)
     * Otherwise the result may be anything including null.
     * @param s_to_t
     * @param u_to_v
     */
    public Set<TRSSubstitution> getConnectingStarSubstitutions(final Node<ProbabilisticRule> from, final Node<ProbabilisticRule> to) {
        final Set<TRSSubstitution> allSubs = new HashSet<>();

        for (final TRSFunctionApplication usableTerm : this.dtToUsableTerms.get(from.getObject().getStandardRepresentation())) {
            for (final Triple<ProbabilisticRule, TRSSubstitution, TRSSubstitution> successorTriple : this.usableTermsToSuccessorWithMGU.get(usableTerm)) {
                if (successorTriple.x.equals(to.getObject().getStandardRepresentation())) {
                    allSubs.add(successorTriple.z);
                }
            }
        }

        return allSubs;
    }

    // ================================================================================
    // Utility
    // ================================================================================

    public String toDOT() {
        return this.g.toDOT(false);
    }

}
