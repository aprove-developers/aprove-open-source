package aprove.verification.probabilistic.Termination.ADPProblem;

import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;

import aprove.*;
import aprove.runtime.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import immutables.*;

/**
 * based on @see aprove.verification.dpframework.DPProblem.QUsableRules
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class ProbQUsableRules {

    // ================================================================================
    // Properties
    // ================================================================================

    private final PQTRSProblem pqtrs;
    private boolean innermost;
    private boolean basic;

    private final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap;

    // a mapping from rules to their nodes
    private Map<ProbabilisticRule, Node<Set<ProbabilisticRule>>> ruleMap;
    // a mapping from function symbols to corresponding rules, repr. R
    private Map<FunctionSymbol, ? extends Set<ProbabilisticRule>> R;
    // a mapping from function symbols to lhss of Q \ lhs(R), if innermost and non-empty set. All with standard prefix vars.
    private Map<FunctionSymbol, Collection<TRSFunctionApplication>> criticalTermsInQ;

    private QTermSet Q;
    // dt to capped adp (in third standard) and corresponding node
    private Map<ProbabilisticRule, Pair<Set<Pair<TRSFunctionApplication, TRSFunctionApplication>>, Node<Set<ProbabilisticRule>>>> dtMap;
    // dp to capped dp (in third standard) and corresponding node
    private Map<Rule, Pair<GeneralizedRule, Node<Set<ProbabilisticRule>>>> dpMap;

    // a mapping from dts to capped lhss wrt. to R^-1, only in termination case and only if R^-1 is non-collapsing
    private Map<ProbabilisticRule, TRSTerm> dtToCappedRminusOneU;
    // a mapping from dts to their usable rules ^-1, only in innermost case
    private Map<ProbabilisticRule, Map<FunctionSymbol, Set<Rule>>> dtToUsedRminusOneST;

    // a mapping from dps to capped lhss wrt. to R^-1, only in termination case and only if R^-1 is non-collapsing
    private Map<Rule, TRSTerm> dpToCappedRminusOneU;
    // a mapping from dps to their usable rules ^-1, only in innermost case
    private Map<Rule, Map<FunctionSymbol, Set<Rule>>> dpToUsedRminusOneST;

    // a mapping from nodes to a scc-nr
    private Map<Node<Set<ProbabilisticRule>>, Integer> nodeToSccNr;
    // a mapping from nodes to qr-normal conditions; null, iff criticalTermsInQ is null iff all terms satisfy condition
    private Map<Node<Set<ProbabilisticRule>>, Boolean> nodeToQRNormal;

    // and a mapping from the nr to the scc; here also singleton nodes with no edges are sccs!
    private Map<Integer, Cycle<Set<ProbabilisticRule>>> nrToScc;

    // a graph where the nodes are the rules in P u R and there is an edge from one rule to another
    // if whenever the first rule is usable, and the conditions in the label are true, then the other rule is also usable
    SimpleGraph<Set<ProbabilisticRule>, QActiveCondition> depGraph;

    private final static TRSVariable Y = TRSVariable.createVariable(TRSTerm.SECOND_STANDARD_PREFIX);

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    public ProbQUsableRules(final PQTRSProblem qtrs, final BidirectionalMap<FunctionSymbol, FunctionSymbol> annoMap) {
        this.pqtrs = qtrs;
        this.annoMap = annoMap;
        init();
    }

    // ================================================================================
    // Accessors
    // ================================================================================

    public PQTRSProblem getUnderlyingPQTRS() {
        return this.pqtrs;
    }

    /**
     * computes whether there is at least one usable rule for a given DP and the
     * underlying QTRS (which was passed in the constructor)
     *
     * @param adp
     * @return true iff the usable rules for this dp are non-empty
     */
    public synchronized boolean hasUsableRules(final ProbabilisticRule adp) {
        final Node<Set<ProbabilisticRule>> node = addADP(adp).y;
        return !this.depGraph.getOut(node).isEmpty();
    }

    /**
     * computes the usable rules for a given ADP and the underlying QTRS (which was
     * passed in the constructor)
     *
     * @param adp
     * @return the set of usable rules, this set may be modified.
     */
    public Set<ProbabilisticRule> getUsableRules(final ProbabilisticRule adp) {
        final ArrayList<ProbabilisticRule> theDp = new ArrayList<>(1);
        theDp.add(adp);
        return this.getUsableRules(theDp);
    }

    /**
     * computes the usable rules for a given set of ADPs and the underlying QTRS
     * (which was passed in the constructor)
     *
     * @param adps
     * @return the set of usable rules, this set may be modified.
     */
    public Set<ProbabilisticRule> getUsableRules(final Collection<ProbabilisticRule> adps) {
        return this.getUsableRules(adps, null);
    }

    /**
     * computes the usable rules for a given set of ADPs, a corresponding Afs, and
     * the underlying QTRS (which was passed in the constructor)
     *
     * @param adps
     * @param afs
     * @return the set of usable rules, this set may be modified.
     */
    public synchronized Set<ProbabilisticRule> getUsableRules(final Collection<ProbabilisticRule> adps,
        final QActiveCondition.Afs afs) {
        final Set<Node<Set<ProbabilisticRule>>> nodesForADPs = addADPs(adps);
        Set<Node<Set<ProbabilisticRule>>> reachable;
        if (afs == null) {
            reachable = this.depGraph.determineReachableNodes(nodesForADPs);
        } else {
            final EdgeFilter<QActiveCondition, Set<ProbabilisticRule>> filter = new EdgeFilter<>() {

                @Override
                public boolean selectEdge(final Node<Set<ProbabilisticRule>> source,
                    final Node<Set<ProbabilisticRule>> dest,
                    final QActiveCondition label) {
                    return label.specialize(afs).isSatisfiable();
                }
            };
            reachable = this.depGraph.determineReachableNodes(nodesForADPs, filter);
        }
        final Set<ProbabilisticRule> usable = new LinkedHashSet<>();
        for (final Node<Set<ProbabilisticRule>> node : reachable) {
            // add rules only of rule nodes!
            if (!nodesForADPs.contains(node)) {
                for (final ProbabilisticRule probRule : node.getObject()) {
                    usable.add(probRule);
                }
            }
        }

        return usable;
    }

    /**
     * computes the usable rules U_A(t) of a term t (annotations are ignored), i.e., all rules whose root
     * symbol occurs in t or (recursively) in the right-hand side of a usable rule
     *
     * @param t
     * @param ruleMap   the rules (by root symbol of their left-hand side)
     * @param deAnnoMap maps annotated to non-annotated symbols
     * @return the set of usable rules, this set may be modified.
     */
    public static Set<ProbabilisticRule> getUsableRulesOfTerm(final TRSTerm t,
        final Map<FunctionSymbol, ? extends Set<ProbabilisticRule>> ruleMap,
        final Map<FunctionSymbol, FunctionSymbol> deAnnoMap) {
        final Set<ProbabilisticRule> usable = new LinkedHashSet<>();
        final Set<FunctionSymbol> seen = new LinkedHashSet<>();
        final Deque<FunctionSymbol> todo = new ArrayDeque<>();
        for (final FunctionSymbol f : t.getFunctionSymbols()) {
            final FunctionSymbol g = deAnnoMap.getOrDefault(f, f);
            if (seen.add(g)) {
                todo.push(g);
            }
        }
        while (!todo.isEmpty()) {
            final Set<ProbabilisticRule> rules = ruleMap.get(todo.pop());
            if (rules != null) {
                for (final ProbabilisticRule rule : rules) {
                    if (usable.add(rule)) {
                        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
                            for (final FunctionSymbol f : entry.getKey().getKey().getFunctionSymbols()) {
                                final FunctionSymbol g = deAnnoMap.getOrDefault(f, f);
                                if (seen.add(g)) {
                                    todo.push(g);
                                }
                            }
                        }
                    }
                }
            }
        }
        return usable;
    }

    /**
     * computes whether the ADP satisfies the qr-Normal condition
     *
     * @param adp
     */
    public synchronized boolean getQRNormal(final ProbabilisticRule adp) {
        if (this.nodeToQRNormal == null) {
            return true;
        } else {
            final Node<Set<ProbabilisticRule>> n = addADP(adp).y;
            return this.nodeToQRNormal.get(n).booleanValue();
        }
    }

    /**
     * computes whether all ADPs satisfy the qr-Normal condition
     *
     * @param adps
     */
    public synchronized boolean getQRNormal(final Iterable<? extends ProbabilisticRule> adps) {
        if (this.nodeToQRNormal == null) {
        } else {
            for (final ProbabilisticRule dp : adps) {
                final Node<Set<ProbabilisticRule>> n = addADP(dp).y;
                final boolean res = this.nodeToQRNormal.get(n).booleanValue();
                if (!res) {
                    return false;
                }
            }
        }
        return true;
    }

    /**
     * returns the capped dp (where variables are only from 2. and 3. standard
     * prefix) Capping was done by renaming the dp to 3. prefix and introducing 2.
     * prefix
     *
     * @param adp
     * @return
     */
    public Set<Pair<TRSFunctionApplication, TRSFunctionApplication>> getCappedDP(final ProbabilisticRule adp) {
        return addADP(adp).x;
    }

    /**
     * computes cap_R^-1(u) (where vars are from 2. prefix). Note that this method
     * may only be called in termination case.
     *
     * @param u_to_v an adp
     */
    public synchronized TRSTerm getCapRminusOneOfU(final ProbabilisticRule u_to_v) {
        if (this.dtToCappedRminusOneU == null) {
            return ProbQUsableRules.Y;
        } else {
            TRSTerm capped = this.dtToCappedRminusOneU.get(u_to_v);
            if (capped == null) {
                capped = ProbQUsableRules.computeCapRminusOne(u_to_v.getLeft(), 0, this.pqtrs.getReverseRuleMap()).x;
                this.dtToCappedRminusOneU.put(u_to_v, capped);
            }
            return capped;
        }
    }

    /**
     * computes Cap^{Sigma_D}_{R^-1}(u) (where vars are from 2. prefix) as needed for the forward instantiation
     * processor for full rewriting: in addition to Cap_{R^-1}(u), all subterms with a (non-annotated) defined
     * root symbol are replaced by fresh variables.
     *
     * @param u              a (possibly annotated) term
     * @param reverseRuleMap the reversed rules R^-1
     * @param defined        the (non-annotated) defined symbols
     */
    public static TRSTerm computeCapRminusOneDefined(final TRSTerm u,
        final Map<FunctionSymbol, ? extends Set<Rule>> reverseRuleMap,
        final Set<FunctionSymbol> defined) {
        if (reverseRuleMap.get(null) != null) { // collapsing, everything can be reached
            return ProbQUsableRules.Y;
        }
        final Pair<TRSTerm, Integer> capped = ProbQUsableRules.computeCapRminusOne(u, 0, reverseRuleMap);
        return ProbQUsableRules.replaceDefinedSubterms(capped.x, new int[] { capped.y }, defined);
    }

    private static TRSTerm replaceDefinedSubterms(final TRSTerm t, final int[] nr, final Set<FunctionSymbol> defined) {
        if (t.isVariable()) {
            return t;
        }
        final TRSFunctionApplication ft = (TRSFunctionApplication) t;
        if (defined.contains(ft.getRootSymbol())) {
            return TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX + "_" + nr[0]++);
        }
        final List<TRSTerm> newArgs = new ArrayList<>(ft.getArguments().size());
        for (final TRSTerm arg : ft.getArguments()) {
            newArgs.add(ProbQUsableRules.replaceDefinedSubterms(arg, nr, defined));
        }
        return TRSTerm.createFunctionApplication(ft.getRootSymbol(), ImmutableCreator.create(newArgs));
    }

    /**
     * computes cap_U(s_to_t,R) (u) (where vars are from 2. prefix). This method may
     * only be called in the innermost case.
     *
     * @param s_to_t an adp
     * @param u_to_v an adp
     * @return
     */
    public TRSTerm getCapUsedRminusOneOfU(final ProbabilisticRule s_to_t, final ProbabilisticRule u_to_v) {
        Map<FunctionSymbol, Set<Rule>> usableRules;
        synchronized (this) {
            usableRules = this.dtToUsedRminusOneST.get(s_to_t);
            if (usableRules == null) {
                usableRules = ProbabilisticRule.getReversedRuleMap(this.getUsableRules(s_to_t));
                this.dtToUsedRminusOneST.put(s_to_t, usableRules);
            }
        }

        if (usableRules.get(null) != null) { // we have a collapsing usable rule
            return ProbQUsableRules.Y;
        } else {
            return ProbQUsableRules.computeCapRminusOne(u_to_v.getLeft(), 0, usableRules).x;
        }
    }

    // ================================================================================
    // Internals
    // ================================================================================

    private void init() {
        if (this.depGraph == null) {
            this.R = this.pqtrs.getRuleMap();
            this.Q = this.pqtrs.getQ();
            this.innermost = this.pqtrs.QsupersetOfLhsR();
            this.basic = this.pqtrs.isBasic();

            // compute qrNormal conditions
            if (this.innermost) {
                final Collection<TRSFunctionApplication> critQTerms = new HashSet<>(this.Q.getTerms());
                for (final ProbabilisticRule rule : this.pqtrs.getPR()) {
                    critQTerms.remove(rule.getLhsInStandardRepresentation());
                }

                if (critQTerms.isEmpty()) {
                    this.criticalTermsInQ = null; // if Q \ lhs(R) is empty, we are trivially qrNormal, as in termination case
                } else {
                    this.criticalTermsInQ = new HashMap<>();
                    this.nodeToQRNormal = new HashMap<>(this.pqtrs.getPR().size());
                    for (final TRSFunctionApplication fterm : critQTerms) {
                        final FunctionSymbol f = fterm.getRootSymbol();
                        Collection<TRSFunctionApplication> critQs = this.criticalTermsInQ.get(f);
                        if (critQs == null) {
                            critQs = new ArrayList<>(4);
                            this.criticalTermsInQ.put(f, critQs);
                        }
                        critQs.add(fterm);
                    }
                }
            } else {
                // in termination case Q supset lhs(R) is not satisfied, hence qrNormal is
                // trivially satisfied
                this.criticalTermsInQ = null;
            }

            // now construct the graph
            this.ruleMap = new LinkedHashMap<>();
            final Set<Node<Set<ProbabilisticRule>>> nodes = new LinkedHashSet<>();
            for (final ProbabilisticRule rule : this.pqtrs.getPR()) {
                final Set<ProbabilisticRule> ruleSet = new LinkedHashSet<>(1);
                ruleSet.add(rule);
                final Node<Set<ProbabilisticRule>> node = new Node<>(ruleSet);
                nodes.add(node);
                this.ruleMap.put(rule, node);
            }

            this.depGraph = new SimpleGraph<>(nodes);

            // now compute all (non-recursive) usable rules and q
            for (final Node<Set<ProbabilisticRule>> node : nodes) {
                Boolean qrNormal = this.criticalTermsInQ != null; // if we trivially satisfy the check, then do no check
                final ProbabilisticRule ruleSchema = node.getObject().iterator().next();
                final ProbabilisticRule probRule = ruleSchema.getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX);
                for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : probRule.getRight().getProbabilityMapping().entrySet()) {
                    final TRSTerm term = entry.getKey().getKey();

                    // TODO: What is qrNormal?
                    qrNormal = addInitialEdges(node, probRule.getLeft(), term, 0, QActiveCondition.TRUE, qrNormal).z;
                }
                // okay, in the trivial case set the proper value
                if (this.criticalTermsInQ != null) {
                    // store qrNormalValue
                    this.nodeToQRNormal.put(node, qrNormal);
                }
            }

            // merge nodes that are combined
            for (final Cycle<Set<ProbabilisticRule>> scc : this.depGraph.getSCCs(ProbQUsableRules.TRUE_FILTER)) {
                mergeRuleNodes(scc);
            }

            // compute sccs and make lookup map for node->#scc and #scc -> scc
            // moreover, propagate qrNormal values
            Integer n = 0;
            this.nrToScc = new HashMap<>();
            this.nodeToSccNr = new HashMap<>(this.R.size());
            for (final Cycle<Set<ProbabilisticRule>> scc : this.depGraph.getSCCs(false)) {
                this.nrToScc.put(n, scc);
                if (this.nodeToQRNormal == null) {
                    // no propagation of qr-Normal values here
                    for (final Node<Set<ProbabilisticRule>> node : scc) {
                        this.nodeToSccNr.put(node, n);
                    }
                } else {
                    boolean qrNormal = true;
                    for (final Node<Set<ProbabilisticRule>> node : scc) {
                        this.nodeToSccNr.put(node, n);
                        if (qrNormal) {
                            qrNormal = this.nodeToQRNormal.get(node).booleanValue();
                        }
                    }

                    if (!qrNormal) {
                        for (final Node<Set<ProbabilisticRule>> node : scc) {
                            for (final Node<Set<ProbabilisticRule>> pred : this.depGraph.getIn(node)) {
                                this.nodeToQRNormal.put(pred, Boolean.FALSE);
                            }
                        }
                    }

                }

                n++;
            }

            // create lookup maps for dts
            this.dtMap = new HashMap<>();
            if (this.innermost || this.basic) {
                this.dtToUsedRminusOneST = new HashMap<>();
            } else {
                if (!this.pqtrs.isCollapsing()) {
                    this.dtToCappedRminusOneU = new HashMap<>();
                }
            }

            // create lookup maps for dps
            this.dpMap = new HashMap<>();
            if (this.innermost || this.basic) {
                this.dpToUsedRminusOneST = new HashMap<>();
            } else {
                if (!this.pqtrs.isCollapsing()) {
                    this.dpToCappedRminusOneU = new HashMap<>();
                }
            }

        }
    }

    private void mergeRuleNodes(final Set<Node<Set<ProbabilisticRule>>> toMerge) {
        final Node<Set<ProbabilisticRule>> collapsed = this.depGraph.merge(toMerge,
            ProbQUsableRules.NODE_UNION_COMBINER,
            ProbQUsableRules.LABEL_OR_COMBINER);
        final boolean nonTrivial = this.criticalTermsInQ != null;
        boolean qrNormal = nonTrivial;
        for (final Node<Set<ProbabilisticRule>> node : toMerge) {
            for (final ProbabilisticRule rule : node.getObject()) {
                this.ruleMap.put(rule, collapsed);
                if (qrNormal) {
                    qrNormal = this.nodeToQRNormal.get(node).booleanValue();
                }
            }
        }

        // store new qrNormal value if needed
        // (if qrNormal was true, then all nodes have true in the end, nothing to
        // change)
        if (nonTrivial && !qrNormal) {
            this.nodeToQRNormal.put(collapsed, Boolean.FALSE);
        }

        this.depGraph.removeEdge(collapsed, collapsed);
    }

    /**
     * adds the ADPs to the graph and returns the corresponding set of nodes
     *
     * @param adps
     * @return the set of nodes for the DPs, the set may be modified
     */
    private Set<Node<Set<ProbabilisticRule>>> addADPs(final Collection<ProbabilisticRule> adps) {
        final Set<Node<Set<ProbabilisticRule>>> res = new LinkedHashSet<>(adps.size());
        for (final ProbabilisticRule dp : adps) {
            res.add(addADP(dp).y);
        }
        return res;
    }

    /**
     * adds an adp to this calculator if not already added, asserts that init() has
     * been called before.
     *
     * @param adp
     * @return the capped dp and the corresponding node
     */
    private synchronized Pair<Set<Pair<TRSFunctionApplication, TRSFunctionApplication>>, Node<Set<ProbabilisticRule>>> addADP(final ProbabilisticRule adp) {
        Pair<Set<Pair<TRSFunctionApplication, TRSFunctionApplication>>, Node<Set<ProbabilisticRule>>> cap_orig_and_node = this.dtMap.get(adp);
        if (cap_orig_and_node == null) {
            final Set<ProbabilisticRule> dpLabel = new HashSet<>(1);
            dpLabel.add(adp);
            final Node<Set<ProbabilisticRule>> n = new Node<>(dpLabel);
            this.depGraph.addNode(n);
            final ProbabilisticRule newAdp = adp.getWithRenumberedVariables(TRSTerm.THIRD_STANDARD_PREFIX);
            final boolean calcQRNormal = this.criticalTermsInQ != null;

            final Set<Pair<TRSFunctionApplication, TRSFunctionApplication>> capp_and_origs = new HashSet<>();

            for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : newAdp.getRight().getProbabilityMapping().entrySet()) {
                final TRSTerm term = entry.getKey().getKey();

                for (final TRSFunctionApplication subterm : term.subAnnoTerms(this.annoMap.getRLMap())) {
                    final Triple<TRSTerm, Integer, Boolean> cap_t_and_qrNormal = addADPEdges(n,
                        newAdp.getLeft(),
                        subterm,
                        0,
                        QActiveCondition.TRUE,
                        calcQRNormal,
                        this.innermost || !this.Q.canBeRewritten(newAdp.getLeft()));
                    if (calcQRNormal) {
                        this.nodeToQRNormal.put(n, cap_t_and_qrNormal.z);
                    }
                    capp_and_origs.add(new Pair<>((TRSFunctionApplication) cap_t_and_qrNormal.x, subterm));
                }
            }

            cap_orig_and_node = new Pair<>(capp_and_origs, n);
            this.dtMap.put(newAdp, cap_orig_and_node);
        }
        return cap_orig_and_node;
    }

    /**
     * the method is very similar to <code>addInitialEdges</code>
     *
     * @param fromNode draw edges from this node
     * @param s        consider this term as lhs
     * @param t        a subterm of the original rhs
     * @param nr       the number for the next free var
     * @param cond     the condition so far
     * @param qrNormal chance to satisfy qrNormal
     * @param sInQNF   is s a Q-normal form or not (in innermost case this value may
     *                 always be true, as a harder check is performed in this
     *                 routine)
     * @return (cap_s(t),next nr for free var, qrNormal can be satisfied) where vars
     *         in cap_s(t) are from 2. and 3. prefix
     */
    //TODO: I think this is currently broken!
    private Triple<TRSTerm, Integer, Boolean> addADPEdges(final Node<Set<ProbabilisticRule>> fromNode,
        final TRSTerm s,
        final TRSTerm t,
        Integer nr,
        final QActiveCondition cond,
        Boolean qrNormal,
        final boolean sInQNF) {
        if (Globals.useAssertions) {
            assert (t.checkVariablePrefix(TRSTerm.THIRD_STANDARD_PREFIX));
            assert (s.checkVariablePrefix(TRSTerm.THIRD_STANDARD_PREFIX));
        }

        if (t.isVariable()) {
            if (this.innermost) {
                return new Triple<>(t, nr, qrNormal);
            } else {
                return new Triple<>(
                    TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX + "_" + nr),
                    nr + 1,
                    qrNormal);
            }
        } else {
            TRSFunctionApplication ft = (TRSFunctionApplication) t;
            final FunctionSymbol f = ft.getRootSymbol();
            final ImmutableList<? extends TRSTerm> args = ft.getArguments();
            final List<TRSTerm> newArgs = new ArrayList<>(args.size());
            int i = 0;
            final Integer oldNr = nr;
            for (final TRSTerm arg : args) {
                final QActiveCondition condArg = cond.and(f, i);
                final Triple<TRSTerm, Integer, Boolean> argRes = addADPEdges(fromNode,
                    s,
                    arg,
                    nr,
                    condArg,
                    qrNormal,
                    sInQNF);
                newArgs.add(argRes.x);
                nr = argRes.y;
                qrNormal = argRes.z;
                i++;
            }
            if (!nr.equals(oldNr)) {
                ft = TRSTerm.createFunctionApplication(f, ImmutableCreator.create(newArgs));
            }

            // now we have the term f(cap(t_1), ..., cap(t_n)) in ft
            // let us check which rules can be connected at top position
            boolean someConnection = false;
            final Set<ProbabilisticRule> possibleRules = this.R.get(f);
            if (possibleRules != null && sInQNF) {
                for (final ProbabilisticRule rule : possibleRules) {
                    final TRSFunctionApplication l = rule.getLhsInStandardRepresentation();
                    boolean drawEdge;
                    if (this.innermost && !Options.certifier.isA3pat() && !Options.certifier.isRainbow()) {
                        final TRSSubstitution sigma = ft.getMGU(l);
                        if (sigma == null) {
                            drawEdge = false;
                        } else {
                            drawEdge = !this.Q.canBeRewritten(s.applySubstitution(sigma))
                                && !this.Q.canBeRewrittenBelowRoot(l.applySubstitution(sigma));
                        }
                    } else {
                        drawEdge = Options.certifier.isA3pat() || Options.certifier.isRainbow() || ft.unifies(l); // a3pat
                                                                                                                 // and
                                                                                                                 // rainbow
                                                                                                                 // can
                                                                                                                 // only
                                                                                                                 // do
                                                                                                                 // EDG!
                    }
                    if (drawEdge) {
                        someConnection = true;
                        final Node<Set<ProbabilisticRule>> ruleNode = this.ruleMap.get(rule);
                        // update qr-normal value from rules
                        if (qrNormal.booleanValue()) {
                            qrNormal = this.nodeToQRNormal.get(ruleNode);
                        }
                        addEdge(fromNode, ruleNode, cond);
                    }
                }
            }

            // and update qrNormal value for this term
            if (this.nodeToQRNormal != null && qrNormal.booleanValue()) {
                final Collection<TRSFunctionApplication> critQs = this.criticalTermsInQ.get(f);
                if (critQs != null) {
                    for (final TRSFunctionApplication critQ : critQs) {
                        if (critQ.unifies(ft)) {
                            qrNormal = Boolean.FALSE;
                            break;
                        }
                    }
                }
            }

            if (someConnection) {
                return new Triple<>(
                    TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX + "_" + nr),
                    nr + 1,
                    qrNormal);
            } else {
                return new Triple<>(ft, nr, qrNormal);
            }
        }
    }

    /**
     * computes CapR^-1(t) where rMinusOne has to be non-Collapsing
     *
     * @param t
     * @param nr
     * @param immutableMap
     * @return the capped term and the next free var, where the capped term has vars
     *         from 2. prefix only
     */
    private static Pair<TRSTerm, Integer> computeCapRminusOne(final TRSTerm t,
        Integer nr,
        final Map<FunctionSymbol, ? extends Set<Rule>> immutableMap) {
        if (Globals.useAssertions) {
            assert (immutableMap.get(null) == null);
        }

        if (t.isVariable()) {
            return new Pair<>(TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX + "_" + nr),
                nr + 1);
        } else {
            TRSFunctionApplication ft = (TRSFunctionApplication) t;
            final FunctionSymbol f = ft.getRootSymbol();
            final ImmutableList<? extends TRSTerm> args = ft.getArguments();
            final List<TRSTerm> newArgs = new ArrayList<>(args.size());
            final Integer oldNr = nr;
            for (final TRSTerm arg : args) {
                final Pair<TRSTerm, Integer> argRes = ProbQUsableRules.computeCapRminusOne(arg, nr, immutableMap);
                newArgs.add(argRes.x);
                nr = argRes.y;
            }
            if (!nr.equals(oldNr)) {
                ft = TRSTerm.createFunctionApplication(f, ImmutableCreator.create(newArgs));
            }

            // now we have the term f(cap(t_1), ..., cap(t_n)) in ft
            // let us check whether some rule unifies at top position
            final Set<Rule> possibleRules = immutableMap.get(f);
            if (possibleRules != null) {
                for (final Rule rule : possibleRules) {
                    final TRSTerm r = rule.getRhsInStandardRepresentation();
                    if (ft.unifies(r)) {
                        return new Pair<>(
                            TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX + "_" + nr),
                            nr + 1);
                    }
                }
            }

            return new Pair<>(ft, nr);
        }
    }

    /**
     * @param fromNode
     * @param l        the lhs of a rule, with variables of THIRD_STANDARD_PREFIX
     * @param r        a (part of) rhs of a rule (l -> C[r]), with variables of
     *                 THIRD_STANDARD_PREFIX
     * @param nr       the next free variable to be chosen
     * @param cond
     * @param qrNormal - have we a chance to satisfy qrNormal up to now?
     * @return the triple (cap(r), new_nr, qrnormal) where new_nr is the next free
     *         variable one can create, and qrnormal is true iff the input qrNormal
     *         is true and for the term r we have that every r does not conflict
     *         with the qr-implies-q-normal condition directly! (without tracking
     *         usable rules) The vars of cap(r) are from 2. and 3. prefix
     */
    private Triple<TRSTerm, Integer, Boolean> addInitialEdges(final Node<Set<ProbabilisticRule>> fromNode,
        final TRSTerm l,
        final TRSTerm r,
        Integer nr,
        final QActiveCondition cond,
        Boolean qrNormal) {
        if (Globals.useAssertions) {
            assert (l.checkVariablePrefix(TRSTerm.THIRD_STANDARD_PREFIX));
            assert (r.checkVariablePrefix(TRSTerm.THIRD_STANDARD_PREFIX));
        }
        if (r.isVariable()) {
            if (this.innermost) {
                return new Triple<>(r, nr, qrNormal);
            } else {
                return new Triple<>(
                    TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX + "_" + nr),
                    nr + 1,
                    qrNormal);
            }
        } else {
            TRSFunctionApplication fr = (TRSFunctionApplication) r;
            final FunctionSymbol f = fr.getRootSymbol();
            final ImmutableList<? extends TRSTerm> args = fr.getArguments();
            final List<TRSTerm> newArgs = new ArrayList<>(args.size());
            int i = 0;
            final Integer oldNr = nr;
            for (final TRSTerm arg : args) {
                final QActiveCondition condArg = cond.and(f, i);
                final Triple<TRSTerm, Integer, Boolean> argRes = addInitialEdges(fromNode,
                    l,
                    arg,
                    nr,
                    condArg,
                    qrNormal);
                newArgs.add(argRes.x);
                nr = argRes.y;
                qrNormal = argRes.z;
                i++;
            }
            if (!nr.equals(oldNr)) {
                fr = TRSTerm.createFunctionApplication(f, ImmutableCreator.create(newArgs));
            }

            // now we have the term f(cap(r_1), ..., cap(r_n)) in fr (with second or third
            // standard prefix vars only)
            // let us check which rules can be connected at top position
            boolean someConnection = false;
            final Set<ProbabilisticRule> possibleRules = this.R.get(f);
            if (possibleRules != null) {
                for (final ProbabilisticRule rule : possibleRules) {
                    final TRSFunctionApplication ruleL = rule.getLhsInStandardRepresentation();
                    if (this.innermost) {
                        // do normal check for computation of cap!
                        final TRSSubstitution sigma = fr.getMGU(ruleL);
                        if (sigma != null) {
                            if (!this.Q.canBeRewrittenBelowRoot(fr.applySubstitution(sigma))) {
                                if (!this.Q.canBeRewrittenBelowRoot(l.applySubstitution(sigma))) {
                                    someConnection = true;
                                    addEdge(fromNode, this.ruleMap.get(rule), cond);
                                }
                            }
                        }
                    } else {
                        if (fr.unifies(ruleL)) {
                            someConnection = true;
                            addEdge(fromNode, this.ruleMap.get(rule), cond);
                        }
                    }
                }
            }

            if (qrNormal.booleanValue()) {
                final Collection<TRSFunctionApplication> critTerms = this.criticalTermsInQ.get(f);
                if (critTerms != null) {
                    for (final TRSFunctionApplication critTerm : critTerms) {
                        if (critTerm.unifies(fr)) {
                            qrNormal = Boolean.FALSE;
                            break;
                        }
                    }
                }
            }

            if (someConnection) {
                return new Triple<>(
                    TRSTerm.createVariable(TRSTerm.SECOND_STANDARD_PREFIX + "_" + nr),
                    nr + 1,
                    qrNormal);
            } else {
                return new Triple<>(fr, nr, qrNormal);
            }
        }
    }

    private void addEdge(final Node<Set<ProbabilisticRule>> from, final Node<Set<ProbabilisticRule>> to, final QActiveCondition cond) {
        if (from != to) {
            this.depGraph.mergeEdge(from, to, cond, ProbQUsableRules.LABEL_OR_COMBINER);
        }
    }

    private static final BinaryOperation<Set<ProbabilisticRule>> NODE_UNION_COMBINER = new BinaryOperation<>() {

        @Override
        public Set<ProbabilisticRule> combine(final Set<ProbabilisticRule> one, final Set<ProbabilisticRule> two) {
            one.addAll(two);
            return one;
        }
    };

    private final static EdgeFilter<QActiveCondition, Set<ProbabilisticRule>> TRUE_FILTER = new EdgeFilter<>() {

        @Override
        public boolean selectEdge(final Node<Set<ProbabilisticRule>> from, final Node<Set<ProbabilisticRule>> to, final QActiveCondition label) {
            return label == QActiveCondition.TRUE;
        }
    };

    private static final BinaryOperation<QActiveCondition> LABEL_OR_COMBINER = new BinaryOperation<>() {

        @Override
        public QActiveCondition combine(final QActiveCondition one, final QActiveCondition two) {
            return one.or(two);
        }
    };

    // ================================================================================
    // Statics
    // ================================================================================

    /**
     * transforms a gives set of rules to pseudo active usable rules (where all
     * conditions are TRUE, so in fact there is no active)
     *
     * @param rules
     * @return
     */
    public static Map<ProbabilisticRule, QActiveCondition> getRulesAsConditionMap(final Collection<ProbabilisticRule> rules) {
        final Map<ProbabilisticRule, QActiveCondition> result = new LinkedHashMap<>(rules.size());
        for (final ProbabilisticRule rule : rules) {
            result.put(rule, QActiveCondition.TRUE);
        }
        return result;
    }

    // ================================================================================
    // Utility
    // ================================================================================

    @Override
    public String toString() {
        final StringBuffer t = new StringBuffer("digraph dp_graph {\nnode [outthreshold=100, inthreshold=100];\n");
        for (final Node<Set<ProbabilisticRule>> node : this.depGraph.getNodes()) {
            t.append(node.getNodeNumber() + " [");
            t.append("label=\"");
            boolean first = true;
            for (final ProbabilisticRule rule : node.getObject()) {
                if (first) {
                    first = false;
                } else {
                    t.append("\\n");
                }
                t.append(rule.toString());
            }
            t.append("\", fontsize=16];\n");
        }
        for (final Edge<QActiveCondition, Set<ProbabilisticRule>> edge : this.depGraph.getEdges()) {
            t.append(edge.getStartNode().getNodeNumber() + " -> " + edge.getEndNode().getNodeNumber());
            t.append("[label=\"" + edge.getObject() + "\"];\n");
        }
        t.append("}\n");
        return t.toString();
    }

}
