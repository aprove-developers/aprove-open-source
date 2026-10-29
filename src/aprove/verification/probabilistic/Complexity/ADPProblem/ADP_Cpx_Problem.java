package aprove.verification.probabilistic.Complexity.ADPProblem;

import java.util.*;
import java.util.Map.*;
import java.util.stream.*;

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
import aprove.verification.probabilistic.Complexity.PTRSProblem.*;
import immutables.*;

/**
 * @author J-C Kassing & Leon Spitzer
 * @version $Id$
 */
public class ADP_Cpx_Problem extends DefaultBasicObligation implements
    Immutable {

    // ================================================================================
    // Properties
    // ================================================================================

    private final QRewriteStrategy strat;
    private final boolean basic;

    // We have a triplet of APDs: <P,S,K>, that keep track of the current state of our DPs
    private final Set<ProbabilisticRule> p_adps; // set of all adps (that contain annotation)
    private final Set<ProbabilisticRule> s_adps; // set of all adps that still need to be proven terminating
    private final Set<ProbabilisticRule> k_adps; // set of all adps that are already proven terminating
    private final PQTRS_Cpx_Problem sWithQ; // contains the usable rules (no annotation)

    /* computed values */
    private volatile ImmutableSet<ProbabilisticRule> usableRules;
    private final ProbComplexityDependencyGraph graph;
    private volatile ImmutableSet<FunctionSymbol> signature;
    private final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    /**
     * creates a Probabilistic-QDP-problem.
     * @param P
     * @param sWithQ
     * @param graph - the graph should be the P-dependency graph
     */
    public ADP_Cpx_Problem(final Set<ProbabilisticRule> p_adps,
        final Set<ProbabilisticRule> s_adps,
        final Set<ProbabilisticRule> k_adps,
        final PQTRS_Cpx_Problem sWithQ,
        final ProbComplexityDependencyGraph graph,
        final QRewriteStrategy strat,
        final boolean basic,
        final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        super("ADP", "Probabilistic DP Problem");

        this.strat = strat;
        this.basic = basic;
        this.p_adps = p_adps;
        this.s_adps = s_adps;
        this.k_adps = k_adps;
        this.sWithQ = sWithQ;
        this.annoMap = annoMap;

        this.graph = graph;
        this.usableRules = ImmutableCreator.create(getProbQUsableRulesCalculator().getUsableRules(this.p_adps));

        final Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.p_adps);
        signature.addAll(CollectionUtils.getFunctionSymbols(this.sWithQ.getPR()));
        this.signature = ImmutableCreator.create(signature);
    }

    /**
     * creates a Probabilistic-QDP-problem.
     * @param sWithQ
     * @param graph - the graph should be the P-dependency graph
     */
    public ADP_Cpx_Problem(final ProbComplexityDependencyGraph graph,
        final Set<ProbabilisticRule> s_adps,
        final Set<ProbabilisticRule> k_adps,
        final PQTRS_Cpx_Problem sWithQ,
        final QRewriteStrategy strat,
        final boolean basic,
        final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        super("ADP", "Probabilistic DP Problem");

        this.strat = strat;
        this.basic = basic;
        this.p_adps = graph.getP();
        this.s_adps = s_adps;
        this.k_adps = k_adps;
        this.sWithQ = sWithQ;
        this.annoMap = annoMap;

        this.graph = graph;
        this.usableRules = ImmutableCreator.create(getProbQUsableRulesCalculator().getUsableRules(this.p_adps));

        final Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.p_adps);
        signature.addAll(CollectionUtils.getFunctionSymbols(this.sWithQ.getPR()));
        this.signature = ImmutableCreator.create(signature);
    }

    /**
     * create a new SAST DP problem from given sets of probabilistic rules P,S,K and the TRS R and the minimal flag.
     * Note that P will be modified!
     * @param P,S,K
     * @param sWithQ
     * @param reachRules
     * @param strat
     * @param basic
     * @return
     */
    public static ADP_Cpx_Problem create(final Set<ProbabilisticRule> p_adps,
        final Set<ProbabilisticRule> s_adps,
        final Set<ProbabilisticRule> k_adps,
        final PQTRS_Cpx_Problem sWithQ,
        final QRewriteStrategy strat,
        final boolean basic,
        final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        final ProbComplexityDependencyGraph graph = ProbComplexityDependencyGraph.create(p_adps, sWithQ, annoMap);
        return new ADP_Cpx_Problem(graph, s_adps, k_adps, sWithQ, strat, basic, annoMap);
    }

    public ADP_Cpx_Problem
        createSubproblem(final ProbComplexityDependencyGraph newGraph, final ImmutableSet<ProbabilisticRule> S, final ImmutableSet<ProbabilisticRule> K) {
        return ADP_Cpx_Problem.create(ImmutableCreator.create(newGraph.getP()), S, K, this.sWithQ, this.strat, this.basic, this.annoMap);
    }

    // ================================================================================
    // Accessors
    // ================================================================================

    public Set<ProbabilisticRule> getP() {
        return this.p_adps;
    }

    public Set<ProbabilisticRule> getS() {
        return this.s_adps;
    }

    public Set<ProbabilisticRule> getK() {
        return this.k_adps;
    }

    public Set<ProbabilisticRule> getSWithQ() {
        return this.sWithQ.getPR();
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

    public Set<FunctionSymbol> getAnnoFunctionSymbols() {
        final Map<FunctionSymbol, FunctionSymbol> annomap = this.annoMap.getLRMap();
        final Set<FunctionSymbol> annosymbols = annomap.values().stream().collect(Collectors.toSet());
        return annosymbols;
    }

    public Map<FunctionSymbol, FunctionSymbol> getDeAnnoMap() {
        return this.annoMap.getRLMap();
    }

    public ImmutableSet<ProbabilisticRule> getUsableRules() {
        return this.usableRules;
    }

    public ProbComplexityDependencyGraph getDependencyGraph() {
        return this.graph;
    }

    public PQTRS_Cpx_Problem getSwithQ() {
        return this.sWithQ;
    }

    public Set<FunctionSymbol> getSignature() {
        return this.signature;
    }

    /**
     * Get the signature of defined symbols including all tuple symbols
     * @return
     */
    public ImmutableSet<FunctionSymbol> getDefSignature() {
        final Set<FunctionSymbol> defSig = new HashSet<>();
        defSig.addAll(this.sWithQ.getDefSymbolsOfR());
        defSig.addAll(getAnnoFunctionSymbols());
        return ImmutableCreator.create(defSig);
    }

    public boolean getInnermost() {
        return this.sWithQ.QsupersetOfLhsR();
    }

    public boolean QsupersetOfLhsS() {
        return this.sWithQ.QsupersetOfLhsR();
    }

    /**
     * @return true, if this SAST_ADPProblem is non-probabilistic i.e. every occurring multidistribution has the form {1:r}.
     * */
    public boolean isNonProbabilistic() {
        for (final ProbabilisticRule pr : this.sWithQ.getPR()) {
            if (!pr.getRight().isDeterministic()) {
                return false;
            }
        }
        for (final ProbabilisticRule depTuple : this.p_adps) {
            if (!depTuple.isDeterministic()) {
                return false;
            }
        }
        return true;
    }

    /**
     * @return set of ProbabilisticRule, for rules which have all predecessors in K_ADPs
     */
    public Set<ProbabilisticRule> getRulesWithAllPredinK() {
        final Set<ProbabilisticRule> rulesWithAllPredinK = new HashSet<>();

        final Set<Node<ProbabilisticRule>> nodes = getDependencyGraph().getGraph().getNodes();
        for (final Node<ProbabilisticRule> node : nodes) {
            // Check if the current node is in S

            if (getS().contains(node.getObject()) && node.getObject().isADP(getDeAnnoMap())) {
                final Set<Node<ProbabilisticRule>> predecessorNodes = getDependencyGraph().getGraph().getIn(node);

                // Transform the set of predecessor nodes to a set of probabilistic rules
                final Set<ProbabilisticRule> predecessorRules = new HashSet<>();
                for (final Node<ProbabilisticRule> n : predecessorNodes) {
                    predecessorRules.add(n.getObject());
                }

                if (getK().containsAll(predecessorRules)) {
                    rulesWithAllPredinK.add(node.getObject());
                }
            }
        }
        return rulesWithAllPredinK;
    }

    /**
     * @return P with only these rules that have annotation in the right hand side
     */
    public Set<ProbabilisticRule> getPwithOnlyAnno() {
        // Create the Set of depTuples that do contain annotation in the right hand side
        final Set<ProbabilisticRule> depTuples = new HashSet<>();
        for (final ProbabilisticRule rule : getP()) {
            for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
                final TRSTerm term = entry.getKey().getKey();
                if (term.countAnnos(getAnnoFunctionSymbols()) > 0) {
                    depTuples.add(rule);
                    break;
                }
            }
        }
        return depTuples;
    }

    /**
     * @return S with only these rules that have annotation in the right hand side
     */
    public Set<ProbabilisticRule> getSwithOnlyAnno() {
        // Create the Set of depTuples that do contain annotation in the right hand side
        final Set<ProbabilisticRule> depTuples = new HashSet<>();
        for (final ProbabilisticRule rule : getS()) {
            for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
                final TRSTerm term = entry.getKey().getKey();
                if (term.countAnnos(getAnnoFunctionSymbols()) > 0) {
                    // one term of the multidistribution contains annotation
                    depTuples.add(rule);
                    break;
                }
            }
        }
        return depTuples;
    }

    public ProbQUsableRules getProbQUsableRulesCalculator() {
        return this.sWithQ.getProbQUsableRulesCalculator(this.annoMap);
    }

    /**
     * @return subproblem with smaller P and the same rewrite strategy as this problem
     */
    public ADP_Cpx_Problem getSubProblem(final ImmutableSet<ProbabilisticRule> P) {

        return this.getSubProblem(this.graph.getSubGraphFromPRules(P));
    }

    /**
     * @return subproblem with some rules in <P,S,K> flattened and the same rewrite strategy as this problem
     */
    public ADP_Cpx_Problem getSubProblemPartiallyFlattened(final Set<ProbabilisticRule> rulesToFlat) {
        if (rulesToFlat.isEmpty()) {
            return this;
        }

        // we need to keep track of P,S,K ADPs
        final Set<ProbabilisticRule> new_p_adps = new HashSet<>();
        final Set<ProbabilisticRule> new_s_adps = new HashSet<>();
        final Set<ProbabilisticRule> new_k_adps = new HashSet<>();

        for (final ProbabilisticRule rule : this.p_adps) {
            if (rulesToFlat.contains(rule)) {
                // we add FLATTENED rule to P ADPs only if rule was contained before
                // we do not add flat rules to S and K
                final ProbabilisticRule flattened_rule = rule.removeAnnos(getDeAnnoMap());

                new_p_adps.add(flattened_rule);

            } else {
                // we add rule to P,S,K ADPs only if rule was contained before
                new_p_adps.add(rule);
                if (this.s_adps.contains(rule)) {
                    new_s_adps.add(rule);
                }
                if (this.k_adps.contains(rule)) {
                    new_k_adps.add(rule);
                }
            }
        }

        final ProbComplexityDependencyGraph new_graph = ProbComplexityDependencyGraph.create(new_p_adps, this.sWithQ, this.annoMap);
        return new ADP_Cpx_Problem(new_p_adps,
            new_s_adps,
            new_k_adps,
            this.sWithQ,
            new_graph,
            this.strat,
            this.basic,
            this.annoMap);
    }

    /**
     * @return subproblem with leaf removed in <P,S,K>
     */
    public ADP_Cpx_Problem getSubProblemWithRemovedLeafs(final Set<ProbabilisticRule> leafRules) {
        if (leafRules.isEmpty()) {
            return this;
        }

        // we need to keep track of P,S,K ADPs
        final Set<ProbabilisticRule> new_p_adps = new HashSet<>();
        final Set<ProbabilisticRule> new_s_adps = new HashSet<>();
        final Set<ProbabilisticRule> new_k_adps = new HashSet<>();

        for (final ProbabilisticRule rule : this.p_adps) {
            if (!leafRules.contains(rule)) {
                // we add all rules that are not leaf rules
                new_p_adps.add(rule);
                // we add rule to S,K ADPs only if rule was contained before
                if (this.s_adps.contains(rule)) {
                    new_s_adps.add(rule);
                }
                if (this.k_adps.contains(rule)) {
                    new_k_adps.add(rule);
                }
            }
        }

        final ProbComplexityDependencyGraph new_graph = ProbComplexityDependencyGraph.create(new_p_adps, this.sWithQ, this.annoMap);
        return new ADP_Cpx_Problem(new_p_adps,
            new_s_adps,
            new_k_adps,
            this.sWithQ,
            new_graph,
            this.strat,
            this.basic,
            this.annoMap);
    }

    /**
     * @return subproblem with some rules moved from S to K
     */
    public ADP_Cpx_Problem getSubProblemWithMovedRules(final Set<ProbabilisticRule> rulesToMove) {
        if (rulesToMove.isEmpty()) {
            return this;
        }

        final Set<ProbabilisticRule> new_s_adps = createCopyOfRulesSet(this.s_adps);
        final Set<ProbabilisticRule> new_k_adps = createCopyOfRulesSet(this.k_adps);

        // we remove rules from S and we add rules to K
        for (final ProbabilisticRule rule : rulesToMove) {
            new_s_adps.remove(rule);
            new_k_adps.add(rule);
        }

        return new ADP_Cpx_Problem(this.p_adps, new_s_adps, new_k_adps, this.sWithQ, this.graph, this.strat, this.basic, this.annoMap);
    }

    /**
     * @return copy of Set<ProbabilisticRule>
     */
    private Set<ProbabilisticRule> createCopyOfRulesSet(final Set<ProbabilisticRule> setOfRules) {
        final Set<ProbabilisticRule> new_set = new HashSet<>();
        for (final ProbabilisticRule rule : setOfRules) {
            new_set.add(rule);
        }
        return new_set;
    }

    /**
     * @param graph
     * @return subproblem with smaller graph and the same rewrite strategy as this problem
     */
    public ADP_Cpx_Problem getSubProblem(final ProbComplexityDependencyGraph graph) {
        if (Globals.useAssertions) {
            assert (this.graph.getGraph().getNodes().containsAll(graph.getGraph().getNodes()));
            assert (this.graph.getGraph().getEdges().containsAll(graph.getGraph().getEdges()));
        }

        return new ADP_Cpx_Problem(graph, this.s_adps, this.k_adps, this.sWithQ, this.strat, this.basic, this.annoMap);
    }

    /**
     * returns a subproblem with R replaced by usable rules. (only in innermost case)
     * this method allows to carry over the usable rule calculation
     * (in contrast to getSubProblemWithSmallerR)
     *
     * @return subproblem with R replaced by usable rules and the same rewrite strategy as this problem
     */
    public ADP_Cpx_Problem getSubProblemWithUsableRules() {
        final PQTRS_Cpx_Problem sWithQ = this.sWithQ.createUsableRulesSubProblem(this);
        final ProbComplexityDependencyGraph subGraph = this.graph.getUsableRulesSubGraph(sWithQ);

        return new ADP_Cpx_Problem(subGraph, this.s_adps, this.k_adps, sWithQ, this.strat, this.basic, this.annoMap);
    }

    /**
     * returns a subproblem with smaller S.
     * Note that unlike getSubProblemWithUsableRules,
     * here the usable-rule calculation cannot be reused.
     *
     * @return subproblem with smaller S and the same rewrite strategy as this problem
     */
    public ADP_Cpx_Problem getSubProblemWithSmallerS(final ImmutableSet<ProbabilisticRule> S) {
        if (Globals.useAssertions) {
            assert (this.sWithQ.getPR().containsAll(S));
        }
        final PQTRS_Cpx_Problem rWithQ = this.sWithQ.createSubProblem(S);
        final ProbComplexityDependencyGraph subGraph = this.graph.getSubGraph(this.p_adps, rWithQ);

        return new ADP_Cpx_Problem(subGraph, this.s_adps, this.k_adps, rWithQ, this.strat, this.basic, this.annoMap);
    }

    /**
     * @return subproblem with irrelevant Q-terms removed and the same rewrite strategy as this problem
     */
    public ADP_Cpx_Problem getSubProblemWithSmallerQ(final QTermSet Q) {
        final PQTRS_Cpx_Problem rWithQ = this.sWithQ.create(Q);
        final ProbComplexityDependencyGraph subGraph = this.graph.getSubGraph(this.p_adps, rWithQ);

        return new ADP_Cpx_Problem(subGraph, this.s_adps, this.k_adps, this.sWithQ, this.strat, this.basic, this.annoMap);
    }

    /**
     * @return subproblem with smaller P and R and the same rewrite strategy as this problem
     */
    public ADP_Cpx_Problem getSubProblem(final Set<ProbabilisticRule> P,
        final ImmutableSet<ProbabilisticRule> S) {
        if (Globals.useAssertions) {
            assert (this.sWithQ.getPR().containsAll(S) && this.p_adps.containsAll(P));
        }
        final PQTRS_Cpx_Problem rWithQ = this.sWithQ.createSubProblem(S);
        final ProbComplexityDependencyGraph subGraph = this.graph.getSubGraph(P, rWithQ);

        return new ADP_Cpx_Problem(subGraph, this.s_adps, this.k_adps, rWithQ, this.strat, this.basic, this.annoMap);
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
        if (getSWithQ().contains(rule)) {
            for (final ProbabilisticRule origRule : getSWithQ()) {
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
        return "posqdt_SAST";
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "SAST");
    }

    @Override
    public String export(final Export_Util eu) {
        final StringBuilder s = new StringBuilder();
        s.append(eu.export("Probabilistic extended ADP Problem:"));
        s.append(eu.linebreak());
        s.append(eu.export("The ADP Problem <P,S> contains following rules with active return value flag:"));
        s.append(eu.linebreak());
        if (getSWithQ().isEmpty()) {
            s.append(eu.export("   none"));
        } else {
            s.append(eu.set(this.sWithQ.getPR(), Export_Util.RULES));
        }
        s.append(eu.linebreak());

        s.append(eu.export("Rules with annotation in P:"));
        s.append(eu.cond_linebreak());
        if (this.p_adps.isEmpty()) {
            s.append(eu.cond_linebreak());
            s.append(eu.export("   none"));
            s.append(eu.cond_linebreak());
        } else {
            s.append(eu.set(this.p_adps, Export_Util.RULES));
        }
        s.append(eu.cond_linebreak());
        s.append(eu.export("Rules with annotation in S:"));
        s.append(eu.cond_linebreak());
        if (this.s_adps.isEmpty()) {
            s.append(eu.cond_linebreak());
            s.append(eu.export("   none"));
            s.append(eu.cond_linebreak());
        } else {
            s.append(eu.set(this.s_adps, Export_Util.RULES));
        }
        s.append(eu.cond_linebreak());
        s.append(eu.export("Rules with annotation and a known complexity:"));
        s.append(eu.cond_linebreak());
        if (this.k_adps.isEmpty()) {
            s.append(eu.cond_linebreak());
            s.append(eu.export("   none"));
        } else {
            s.append(eu.set(this.k_adps, Export_Util.RULES));
        }
        s.append(eu.cond_linebreak());

        return s.toString();
    }

    @Override
    public String toString() {
        return export(new PLAIN_Util());
    }

    public Pair<ADP_Cpx_Problem, Integer>
        getTransformedProblem(final ADP_Cpx_Transformation transformation,
            final Node<ProbabilisticRule> origNode,
            final Set<ProbabilisticRule> newDTs,
            final Set<ProbabilisticRule> newRules,
            final Position p) {

        final Pair<ProbComplexityDependencyGraph, Integer> graphCounter = this.graph.getTransformedGraph(transformation,
            origNode,
            newDTs,
            newRules,
            p);

        final Set<ProbabilisticRule> newS = new HashSet<>(this.s_adps);
        for (final ProbabilisticRule s_rule : this.s_adps) {
            if (s_rule.equals(origNode.getObject())) {
                newS.remove(s_rule);
                newS.addAll(newDTs);
                break;
            }
        }
        final Set<ProbabilisticRule> newK = new HashSet<>(this.k_adps);
        for (final ProbabilisticRule k_rule : this.k_adps) {
            if (k_rule.equals(origNode.getObject())) {
                newK.remove(k_rule);
                newK.addAll(newDTs);
                break;
            }
        }

        final Set<ProbabilisticRule> newPR = new HashSet<>();
        newPR.addAll(this.sWithQ.getPR());
        newPR.addAll(newRules);
        final PQTRS_Cpx_Problem newPQTRS =
            PQTRS_Cpx_Problem.create(ImmutableCreator.create(newPR), this.sWithQ.getQ(), this.sWithQ.getStrat(), this.sWithQ.isBasic());

        return new Pair<>(new ADP_Cpx_Problem(graphCounter.x, newS, newK, newPQTRS, this.strat, this.basic, this.annoMap),
            graphCounter.y);
    }

    //TODO: Equals Methode

}
