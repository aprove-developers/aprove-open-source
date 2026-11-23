package aprove.verification.probabilistic.Termination.ADPProblem.AST;

import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;

import aprove.*;
import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.ADPProblem.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import immutables.*;

/**
 * @author J-C Kassing
 * @version $Id$
 */
public class ADP_AST_Problem extends DefaultBasicObligation implements
    Immutable {

    // ================================================================================
    // Properties
    // ================================================================================

    private final QRewriteStrategy strat;
    private final boolean basic;

    private final Set<ProbabilisticRule> adps;
    private final PQTRSProblem sWithQ; //This contains the rules with active flag

    /* computed values */
    private final ProbQDependencyGraph graph;
    private volatile ImmutableSet<ProbabilisticRule> usableRules; //subset of rules in sWithQ

    private volatile ImmutableSet<FunctionSymbol> signature;

    private final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap;

    /**BASIC**/
    //We assume that the following attributes are null, if the problem is not basic.
    private final Set<ProbabilisticRule> reachADPs; //superset of adps containing IuP
    private final PQTRSProblem reachRules; //This contains the rules with active flag
                                          //superset of sWithQ containing I^true u P^true
                                          /* computed values */
    private final ProbQDependencyGraph reachGraph; //reachGraph is always a super graph of "graph" 
                                                  //with the reachability rules containing nodes IuP
    private volatile ImmutableSet<ProbabilisticRule> basicUsableRules; //subset of rules in reachRules

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    /**
     * creates a (non-basic) Probabilistic-ADP-problem.
     * @param P
     * @param sWithQ
     * @param graph - the graph should be the P-dependency graph
     */
    public ADP_AST_Problem(final Set<ProbabilisticRule> probabilisticDependencyTuples,
        final ProbQDependencyGraph graph,
        final PQTRSProblem sWithQ,
        final QRewriteStrategy strat,
        final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        super("ADP", "Probabilistic DP Problem");

        this.strat = strat;
        this.basic = false;
        this.adps = probabilisticDependencyTuples;
        this.sWithQ = sWithQ;
        this.annoMap = annoMap;

        this.graph = graph;
        this.usableRules = ImmutableCreator.create(getProbQUsableRulesCalculator().getUsableRules(this.adps));

        final Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.adps);
        signature.addAll(CollectionUtils.getFunctionSymbols(this.sWithQ.getPR()));
        this.signature = ImmutableCreator.create(signature);

        this.reachADPs = null;
        this.reachRules = null;
        this.reachGraph = null;
        this.basicUsableRules = null;
    }

    /**
     * creates a basic Probabilistic-QDP-problem.
     * @param P
     * @param sWithQ
     * @param graph - the graph should be the P-dependency graph
     */
    public ADP_AST_Problem(final Set<ProbabilisticRule> probabilisticDependencyTuples,
        final Set<ProbabilisticRule> reachADPs,
        final ProbQDependencyGraph graph,
        final ProbQDependencyGraph reachGraph,
        final PQTRSProblem sWithQ,
        final PQTRSProblem reachRules,
        final QRewriteStrategy strat,
        final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        super("ADP", "Probabilistic DP Problem");

        this.strat = strat;
        this.basic = true;
        this.adps = probabilisticDependencyTuples;
        this.sWithQ = sWithQ;
        this.annoMap = annoMap;

        this.graph = graph;
        this.usableRules = ImmutableCreator.create(getProbQUsableRulesCalculator().getUsableRules(this.adps));

        final Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.adps);
        signature.addAll(CollectionUtils.getFunctionSymbols(this.sWithQ.getPR()));
        this.signature = ImmutableCreator.create(signature);

        this.reachADPs = reachADPs;
        this.reachRules = reachRules;
        this.reachGraph = reachGraph;
        this.basicUsableRules = ImmutableCreator.create(getProbQBasicUsableRulesCalculator().getUsableRules(this.reachADPs));
    }

    /**
     * creates a (non-basic) Probabilistic-QDP-problem.
     * @param sWithQ
     * @param graph - the graph should be the P-dependency graph
     */
    public ADP_AST_Problem(final ProbQDependencyGraph graph,
        final PQTRSProblem sWithQ,
        final QRewriteStrategy strat,
        final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        super("ADP", "Probabilistic DP Problem");

        this.strat = strat;
        this.basic = false;
        this.adps = graph.getP();
        this.sWithQ = sWithQ;
        this.annoMap = annoMap;

        this.graph = graph;
        this.usableRules = ImmutableCreator.create(getProbQUsableRulesCalculator().getUsableRules(this.adps));

        final Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.adps);
        signature.addAll(CollectionUtils.getFunctionSymbols(this.sWithQ.getPR()));
        this.signature = ImmutableCreator.create(signature);

        this.reachADPs = null;
        this.reachRules = null;
        this.reachGraph = null;
        this.basicUsableRules = null;
    }

    /**
     * creates a basic Probabilistic-QDP-problem.
     * @param sWithQ
     * @param graph - the graph should be the P-dependency graph
     */
    public ADP_AST_Problem(final ProbQDependencyGraph graph,
        final ProbQDependencyGraph reachGraph,
        final PQTRSProblem sWithQ,
        final PQTRSProblem reachRules,
        final QRewriteStrategy strat,
        final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        super("ADP", "Probabilistic DP Problem");

        this.strat = strat;
        this.basic = true;
        this.adps = graph.getP();
        this.sWithQ = sWithQ;
        this.annoMap = annoMap;

        this.graph = graph;
        this.usableRules = ImmutableCreator.create(getProbQUsableRulesCalculator().getUsableRules(this.adps));

        final Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.adps);
        signature.addAll(CollectionUtils.getFunctionSymbols(this.sWithQ.getPR()));
        this.signature = ImmutableCreator.create(signature);

        this.reachADPs = reachGraph.getP();
        this.reachRules = reachRules;
        this.reachGraph = reachGraph;
        this.basicUsableRules = ImmutableCreator.create(getProbQBasicUsableRulesCalculator().getUsableRules(this.reachADPs));

    }

    /**
     * Create a new (non-basic) DP problem from a given graph P
     * over the ADPs and the PTRS S.
     * Note that P will be modified!
     * @param P - Graph containing the ADPs
     * @param sWithQ - PTRS with usable rules
     * @param strat - The rewrite strategy to analyze
     * @param annoMap - Map to distinguish annotated and non-annotated symbols
     * @return AST_ADPProblem
     */
    public static ADP_AST_Problem create(final Graph<ProbabilisticRule, ?> P,
        final PQTRSProblem sWithQ,
        final QRewriteStrategy strat,
        final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        final ProbQDependencyGraph graph = ProbQDependencyGraph.create(P, sWithQ, annoMap);
        return new ADP_AST_Problem(graph, sWithQ, strat, annoMap);
    }

    /**
     * Create a new basic DP problem from a given graph P
     * over the ADPs and the PTRS S.
     * Note that P will be modified!
     * @param P - Graph containing the ADPs of P
     * @param P - Graph containing the ADPs of IuP
     * @param sWithQ - PTRS with usable rules
     * @param reachRules - PTRS with usable rules of IuP
     * @param strat - The rewrite strategy to analyze
     * @param annoMap - Map to distinguish annotated and non-annotated symbols
     * @return AST_ADPProblem
     */
    public static ADP_AST_Problem createBasic(final Graph<ProbabilisticRule, ?> P,
        final Graph<ProbabilisticRule, ?> D,
        final PQTRSProblem sWithQ,
        final PQTRSProblem reachRules,
        final QRewriteStrategy strat,
        final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        final ProbQDependencyGraph graph = ProbQDependencyGraph.create(P, sWithQ, annoMap);
        final ProbQDependencyGraph reachGraph = ProbQDependencyGraph.create(D, reachRules, annoMap);
        return new ADP_AST_Problem(graph, reachGraph, sWithQ, reachRules, strat, annoMap);
    }

    /**
     * Create a new (non-basic) DP problem from a given set of ADPs and the PTRS S.
     * Note that P will be modified!
     * @param P - ADPs
     * @param sWithQ - PTRS with usable rules
     * @param strat - The rewrite strategy to analyze
     * @param annoMap - Map to distinguish annotated and non-annotated symbols
     * @return AST_ADPProblem
     */
    public static ADP_AST_Problem create(final Set<ProbabilisticRule> P,
        final PQTRSProblem sWithQ,
        final QRewriteStrategy strat,
        final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        final ProbQDependencyGraph graph = ProbQDependencyGraph.create(P, sWithQ, annoMap);
        return new ADP_AST_Problem(graph, sWithQ, strat, annoMap);
    }

    /**
     * Create a new basic DP problem from a given set of ADPs and the PTRS S.
     * Note that P will be modified!
     * @param P - ADPs of P
     * @param D - ADPs of IuP
     * @param sWithQ - PTRS with usable rules of P
     * @param reachRules - PTRS with usable rules of IuP
     * @param strat - The rewrite strategy to analyze
     * @param annoMap - Map to distinguish annotated and non-annotated symbols
     * @return AST_ADPProblem
     */
    public static ADP_AST_Problem createBasic(final Set<ProbabilisticRule> P,
        final Set<ProbabilisticRule> D,
        final PQTRSProblem sWithQ,
        final PQTRSProblem reachRules,
        final QRewriteStrategy strat,
        final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        final ProbQDependencyGraph graph = ProbQDependencyGraph.create(P, sWithQ, annoMap);
        final ProbQDependencyGraph reachGraph = ProbQDependencyGraph.create(D, reachRules, annoMap);
        return new ADP_AST_Problem(graph, reachGraph, sWithQ, reachRules, strat, annoMap);
    }

    /**
     * Create a new (non-basic) DP problem from a given Prob dependency graph and the PTRS S.
     * Note that P will be modified!
     * @param sWithQ - PTRS with usable rules
     * @param graph - Prob dependency graph over the ADPs
     * @param strat - The rewrite strategy to analyze
     * @param annoMap - Map to distinguish annotated and non-annotated symbols
     * @return AST_ADPProblem
     */
    public static ADP_AST_Problem create(final PQTRSProblem sWithQ,
        final ProbQDependencyGraph graph,
        final QRewriteStrategy strat,
        final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        return new ADP_AST_Problem(graph, sWithQ, strat, annoMap);
    }

    /**
     * Create a new basic DP problem from a given Prob dependency graph and the PTRS S.
     * Note that P will be modified!
     * @param sWithQ - PTRS with usable rules of P
     * @param reachRules - PTRS with usable rules of IuP
     * @param graph - Prob dependency graph over the ADPs of P
     * @param reachGraph - Prob dependency graph over the ADPs of IuP
     * @param strat - The rewrite strategy to analyze
     * @param annoMap - Map to distinguish annotated and non-annotated symbols
     * @return AST_ADPProblem
     */
    public static ADP_AST_Problem createBasic(final PQTRSProblem sWithQ,
        final PQTRSProblem reachRules,
        final ProbQDependencyGraph graph,
        final ProbQDependencyGraph reachGraph,
        final QRewriteStrategy strat,
        final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        return new ADP_AST_Problem(graph, reachGraph, sWithQ, reachRules, strat, annoMap);
    }

    // ================================================================================
    // Accessors
    // ================================================================================

    public Set<ProbabilisticRule> getP() {
        return this.adps;
    }

    public Set<ProbabilisticRule> getS() {
        return this.sWithQ.getPR();
    }

    public Set<ProbabilisticRule> getReach() {
        return this.reachADPs;
    }

    public Set<ProbabilisticRule> getReachRules() {
        return this.reachRules.getPR();
    }

    public QTermSet getQ() {
        return this.sWithQ.getQ();
    }

    public QRewriteStrategy getStrat() {
        return this.strat;
    }

    public boolean isBasic() {
        return this.basic;
    }

    public BidirectionalMap<FunctionSymbol, FunctionSymbol> getBiAnnoMap() {
        return this.annoMap;
    }

    public Map<FunctionSymbol, FunctionSymbol> getAnnoMap() {
        return this.annoMap.getLRMap();
    }

    public Map<FunctionSymbol, FunctionSymbol> getDeAnnoMap() {
        return this.annoMap.getRLMap();
    }

    public ImmutableSet<ProbabilisticRule> getUsableRules() {
        return this.usableRules;
    }

    public ImmutableSet<ProbabilisticRule> getBasicUsableRules() {
        return this.basicUsableRules;
    }

    public ProbQDependencyGraph getDependencyGraph() {
        return this.graph;
    }

    public ProbQDependencyGraph getReachDependencyGraph() {
        return this.reachGraph;
    }

    public PQTRSProblem getSwithQ() {
        return this.sWithQ;
    }

    public PQTRSProblem getReachPQTRS() {
        return this.reachRules;
    }

    /**
     * (Only for basic problems)
     *
     * Returns a new AST_PosQDT-Problem where origNode (from the dependency graph) is transformed by nri to a set of new
     * DPs. Moreover, the counter for the new DPs and the given transformation is returned.
     * @param origNode
     * @param newDTs
     * @param p - the position of the transformation in t.
     * @return the counter for the new DPs and the given transformation.
     */
    public Pair<ADP_AST_Problem, Integer>
        getTransformedProblemInitialADPs(final ADP_AST_Transformation transformation,
            final Node<ProbabilisticRule> origNode,
            final Set<ProbabilisticRule> newDTs,
            final Set<ProbabilisticRule> newRules,
            final Position p) {

        final Pair<ProbQDependencyGraph, Integer> graphCounter = this.graph.getTransformedGraph(transformation,
            origNode,
            newDTs,
            newRules,
            p);

        final Set<ProbabilisticRule> newPR = new HashSet<>();
        newPR.addAll(this.sWithQ.getPR());
        newPR.addAll(newRules);
        final PQTRSProblem newPQTRS =
            PQTRSProblem.create(ImmutableCreator.create(newPR), this.sWithQ.getQ(), this.sWithQ.getStrat(), this.sWithQ.getTarget(), this.sWithQ.isBasic());

        return new Pair<>(new ADP_AST_Problem(this.graph, graphCounter.x, this.sWithQ, newPQTRS, this.strat, this.annoMap),
            graphCounter.y);
    }

    /**
     * Returns a new AST_PosQDT-Problem where origNode (from reachDepGraph) is transformed by nri to a set of new
     * DPs. Moreover, the counter for the new DPs and the given transformation is returned.
     * @param origNode
     * @param newDTs
     * @param p - the position of the transformation in t.
     * @return the counter for the new DPs and the given transformation.
     */
    public Pair<ADP_AST_Problem, Integer>
        getTransformedProblem(final ADP_AST_Transformation transformation,
            final Node<ProbabilisticRule> origNode,
            final Set<ProbabilisticRule> newDTs,
            final Set<ProbabilisticRule> newRules,
            final Position p) {

        final Pair<ProbQDependencyGraph, Integer> graphCounter = this.graph.getTransformedGraph(transformation,
            origNode,
            newDTs,
            newRules,
            p);

        final Set<ProbabilisticRule> newPR = new HashSet<>();
        newPR.addAll(this.sWithQ.getPR());
        newPR.addAll(newRules);
        final PQTRSProblem newPQTRS =
            PQTRSProblem.create(ImmutableCreator.create(newPR), this.sWithQ.getQ(), this.sWithQ.getStrat(), this.sWithQ.getTarget(), this.sWithQ.isBasic());

        if (this.basic) {
            /**BASIC**/
            final Node<ProbabilisticRule> basicNode = this.reachGraph.getGraph().getNodeFromObject(origNode.getObject());

            final Pair<ProbQDependencyGraph, Integer> reachGraphCounter = this.reachGraph.getTransformedGraph(transformation,
                basicNode,
                newDTs,
                newRules,
                p);

            final Set<ProbabilisticRule> newPRReach = new HashSet<>();
            newPRReach.addAll(this.reachRules.getPR());
            newPRReach.addAll(newRules);
            final PQTRSProblem newPQTRSReach = PQTRSProblem.create(ImmutableCreator
                .create(newPRReach), this.reachRules.getQ(), this.reachRules.getStrat(), this.reachRules.getTarget(), this.reachRules.isBasic());

            return new Pair<>(
                new ADP_AST_Problem(graphCounter.x, reachGraphCounter.x, newPQTRS, newPQTRSReach, this.strat, this.annoMap),
                graphCounter.y);
        } else { /**FULL and INNERMOST**/
            return new Pair<>(new ADP_AST_Problem(graphCounter.x, newPQTRS, this.strat, this.annoMap), graphCounter.y);
        }
    }

    public Set<FunctionSymbol> getSignature() {
        return this.signature;
    }

    public ImmutableSet<FunctionSymbol> getDPSymbols() {
        return ImmutableCreator.create(this.annoMap.getRLMap().keySet());
    }

    public ImmutableSet<Rule> getNonProbDPs() {
        final Set<Rule> depPairs = new HashSet<>();
        for (final ProbabilisticRule depTuple : this.adps) {
            for (final TRSTerm rhs : depTuple.getRight().getSupport()) {
                for (final TRSTerm annoSubterm : rhs.getAnnoSubterms(getDeAnnoMap())) {
                    depPairs.add(Rule.create(depTuple.getLeft(), annoSubterm));
                }
            }
        }
        return ImmutableCreator.create(depPairs);
    }

    public boolean isInnermost() {
        // basic ADP problems are only created for full rewriting (if the set of active rules becomes empty
        // by the usable rules processor, then Q is trivially a superset of lhs(S), but this is no innermost problem)
        return !this.basic && this.sWithQ.QsupersetOfLhsR();
    }

    /**
     * @return true, if this AST_ADPProblem is non-probabilistic i.e. every occurring multidistribution has the form {1:r}.
     * */
    public boolean isNonProbabilistic() {
        for (final ProbabilisticRule pr : this.sWithQ.getPR()) {
            if (!pr.getRight().isDeterministic()) {
                return false;
            }
        }
        for (final ProbabilisticRule depTuple : this.adps) {
            if (!depTuple.isDeterministic()) {
                return false;
            }
        }
        return true;
    }

    /**
     * @return true, if every term r_i in a right-hand side {p_1:r_1, ..., p_k:r_k} contains only a single annotation.
     * */
    public boolean hasSingleAnnotationInADPs() {
        for (final ProbabilisticRule adp : this.adps) {
            for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : adp.getRight().getProbabilityMapping().entrySet()) {
                final TRSTerm rhs = entry.getKey().getKey();
                if (rhs.countAnnos(getDPSymbols()) > 1) {
                    return false;
                }
            }
        }
        return true;
    }

    public ProbQUsableRules getProbQUsableRulesCalculator() {
        return this.sWithQ.getProbQUsableRulesCalculator(this.annoMap);
    }

    public ProbQUsableRules getProbQBasicUsableRulesCalculator() {
        return this.reachRules.getProbQUsableRulesCalculator(this.annoMap);
    }

    /**
     * @return subproblem with smaller P and the same rewrite strategy as this problem
     */
    public ADP_AST_Problem getSubProblem(final ImmutableSet<ProbabilisticRule> P) {
        return this.getSubProblem(this.graph.getSubGraphFromPRules(P));
    }

    /**
     * Use only for non-basic problems!
     *
     * @param graph
     * @return subproblem with smaller graph and the same rewrite strategy as this problem
     */
    public ADP_AST_Problem getSubProblem(final ProbQDependencyGraph graph) {
        if (Globals.useAssertions) {
            assert (!this.basic);
            assert (this.graph.getGraph().getNodes().containsAll(graph.getGraph().getNodes()));
            assert (this.graph.getGraph().getEdges().containsAll(graph.getGraph().getEdges()));
        }

        return new ADP_AST_Problem(graph, this.sWithQ, this.strat, this.annoMap);
    }

    /**
     * Use only for basic problems!
     *
     * @param graph
     * @return subproblem with smaller graph and the same rewrite strategy as this problem
     */
    public ADP_AST_Problem getSubProblemWithReachability(final ProbQDependencyGraph graph) {
        if (Globals.useAssertions) {
            assert (this.basic);
            assert (this.graph.getGraph().getNodes().containsAll(graph.getGraph().getNodes()));
            assert (this.graph.getGraph().getEdges().containsAll(graph.getGraph().getEdges()));
        }

        final Set<Node<ProbabilisticRule>> reachingNodes = new HashSet<>();
        final Set<Node<ProbabilisticRule>> nodesToReach = graph.getGraph().getNodes();

        for (final Node<ProbabilisticRule> node : this.reachGraph.getGraph().getNodes()) {
            for (final Node<ProbabilisticRule> nodeToReach : nodesToReach) {
                final Node<ProbabilisticRule> nodeInReachGraph = this.reachGraph.getGraph().getNodeFromObject(nodeToReach.getObject());
                if (this.reachGraph.getGraph().hasPath(node, nodeInReachGraph, true, null)) {
                    reachingNodes.add(node);
                }
            }
        }

        return new ADP_AST_Problem(graph, this.reachGraph.getSubGraph(reachingNodes), this.sWithQ, this.reachRules, this.strat, this.annoMap);
    }

    /**
     * Use only for non-basic problems!
     *
     * Returns a subproblem with R replaced by usable rules.
     * This method allows to carry over the usable rule calculation.
     * (in contrast to getSubProblemWithSmallerR)
     *
     * @return subproblem with R replaced by usable rules and the same rewrite strategy as this problem
     */
    public ADP_AST_Problem getSubProblemWithUsableRules() {
        if (Globals.useAssertions) {
            assert (!this.basic);
        }

        final PQTRSProblem sWithQ = this.sWithQ.createUsableRulesSubProblem(this);
        final ProbQDependencyGraph subGraph = this.graph.getUsableRulesSubGraph(sWithQ);

        return new ADP_AST_Problem(subGraph, sWithQ, this.strat, this.annoMap);
    }

    /**
     * Use only for basic problems!
     *
     * Returns a subproblem with R replaced by usable rules.
     * This method allows to carry over the usable rule calculation.
     * (in contrast to getSubProblemWithSmallerR)
     *
     * @return subproblem with R replaced by usable rules and the same rewrite strategy as this problem
     */
    public ADP_AST_Problem getSubProblemWithBasicUsableRules() {
        if (Globals.useAssertions) {
            assert (this.basic);
        }

        final PQTRSProblem reachRules = this.reachRules.createBasicUsableRulesSubProblem(this);

        final Set<ProbabilisticRule> basicUsable = new HashSet<>();
        for (final ProbabilisticRule pr : reachRules.getPR()) {
            if (this.sWithQ.getPR().contains(pr)) {
                basicUsable.add(pr);
            }
        }

        final PQTRSProblem sWithQ = this.sWithQ.createSubProblem(ImmutableCreator.create(basicUsable));
        final ProbQDependencyGraph subGraph = this.graph.getUsableRulesSubGraph(sWithQ);

        final PQTRSProblem newReachRules = this.reachRules.createSubProblem(ImmutableCreator.create(this.basicUsableRules));
        final ProbQDependencyGraph subReachGraph = this.reachGraph.getUsableRulesSubGraph(newReachRules);

        return new ADP_AST_Problem(subGraph, subReachGraph, sWithQ, newReachRules, this.strat, this.annoMap);
    }

    /**
     * Return an identical DT to the input.
     * If this input already occurs as DT, then this is returned
     * (so, the variable names of the already present pair are taken)
     * @param pair
     * @return
     */
    public ProbabilisticRule getDT(final ProbabilisticRule dt) {
        if (getP().contains(dt)) {
            for (final ProbabilisticRule origPair : getP()) {
                if (origPair.equals(dt)) {
                    return origPair;
                }
            }
        }
        return dt;
    }

    /**
     * Return an identical probabilistic rule to the input.
     * If this input already occurs as rule, then this is returned
     * (so, the variable names of the already present pair are taken)
     * @param pair
     * @return
     */
    public ProbabilisticRule getRule(final ProbabilisticRule rule) {
        if (getS().contains(rule)) {
            for (final ProbabilisticRule origRule : getS()) {
                if (origRule.equals(rule)) {
                    return origRule;
                }
            }
        }
        return rule;
    }

    // ================================================================================
    // Utility
    // ================================================================================

    @Override
    public String getStrategyName() {
        return "posqdt_AST";
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "AST");
    }

    @Override
    public String export(final Export_Util eu) {
        final StringBuilder s = new StringBuilder();
        s.append(eu.export("Probabilistic ADP Problem:"));
        s.append(eu.cond_linebreak());

        if (getS().isEmpty()) {
            s.append("The set of rules with active return value flag is empty.");
            s.append(eu.linebreak());
        } else {
            s.append(eu.export("The ADP Problem has the following rules with active return value flag:"));
            s.append(eu.cond_linebreak());
            s.append(eu.set(this.sWithQ.getPR(), Export_Util.RULES));
            s.append(eu.cond_linebreak());
        }

        if (getP().isEmpty()) {
            s.append("The set of rules with annotations is empty.");
            s.append(eu.linebreak());
        } else {
            s.append(eu.export("The ADP Problem has the following rules with annotations:"));
            s.append(eu.cond_linebreak());
            s.append(eu.set(this.adps, Export_Util.RULES));
            s.append(eu.cond_linebreak());
        }

        if (this.basic) {
            /**BASIC**/

            final Set<ProbabilisticRule> onlyReachRules = new HashSet<>();
            for (final ProbabilisticRule rule : this.reachADPs) {
                if (!this.adps.contains(rule)) {
                    onlyReachRules.add(rule);
                }
            }

            if (onlyReachRules.isEmpty()) {
                s.append("The additional set of rules for the reachability analysis is empty.");
                s.append(eu.linebreak());
            } else {
                s.append(eu.export("The ADP Problem has the following additional rules with annotations for the reachability analysis:"));
                s.append(eu.cond_linebreak());
                s.append(eu.set(onlyReachRules, Export_Util.RULES));
                s.append(eu.cond_linebreak());
            }
        }

        return s.toString();
    }

    @Override
    public String toString() {
        return export(new PLAIN_Util());
    }

    //TODO: Equals Methode

}
