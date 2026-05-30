package aprove.verification.confluence;

import java.util.*;
import java.util.stream.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.verification.confluence.Utility.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Output.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.Graph.Node;
import aprove.xml.*;
import immutables.*;



/**
 * Represents a confluence problem for a TRS.
 * It contains the rules of the TRS, the signature, and some cached values.
 * It also provides methods to calculate critical pairs and to check for recursive symbols.
 */
public class ConfTRSProblem extends DefaultBasicObligation
                            implements
                            HTML_Able,
                            HasTRSTerms,
                            ExternUsable {

    private final ImmutableSet<Rule> rules;

    // cached / calculated values
    private final int hashCode;
    private volatile CriticalPairs critPairs;
    private Integer maxArity;
    private final ImmutableSet<FunctionSymbol> signature;        // signature of R
    private volatile ImmutableSet<FunctionSymbol> defSymbolsOfR;        // the same as ruleMap.keySet();
    private volatile ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> ruleMap;
    private volatile ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> reverseRuleMap; // a map from symbols of rhs to rules (which have to read from right to left!),

    private static boolean checkConstructorArgs(final ImmutableSet<Rule> R) {
        return R != null;
    }

    private Boolean isNonOverlapping;

    private Boolean isLeftLinear;
    private Boolean isLinear;
    private Boolean isNotLayerPreserving;

    private volatile ImmutableSet<FunctionSymbol> sharedConstructorSymbols; // forall c: forall l->r/in R: root(l) != c
    private volatile ImmutableSet<FunctionSymbol> sharedLayerPreservingConstructorSymbols;
    private volatile ImmutableSet<FunctionSymbol> nonLayerPreservingConstructorSymbols;

    private QTRSProblem termination;
    
    private QTRSProblem innermostTermination;

    private SimpleGraph<FunctionSymbol, Object> functionDependencyGraph;

    private Map<FunctionSymbol, Node<FunctionSymbol>> functionDependencyGraphNodeMap;
    
    private SimpleGraph<ImmutableLinkedHashSet<FunctionSymbol>, Void> condencedDepGraph;

    /**
     * creates a Confluence Problem for a simple TRS.
     * @param rules - the TRS
     */
    private ConfTRSProblem(final ImmutableSet<Rule> rules) {
        super("ConfTRS", "Confluence Problem of a TRS");
        assert (ConfTRSProblem.checkConstructorArgs(rules));
        this.rules = rules;
        this.hashCode = this.rules.hashCode() * 849332 + 840213;
        this.critPairs = null;
        this.maxArity = null;
        this.defSymbolsOfR = null;
        this.ruleMap = null;
        this.reverseRuleMap = null;
        Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.rules);
        this.signature = ImmutableCreator.create(signature);
        this.calculateDefSymbolsAndRuleMap();

        this.isNonOverlapping = null;

        this.isLeftLinear = null;
        this.isLinear = null;
        this.isNotLayerPreserving = null;

        this.sharedConstructorSymbols = null;
        this.sharedLayerPreservingConstructorSymbols = null;

        this.functionDependencyGraph = null;
        this.functionDependencyGraphNodeMap = null;
        this.condencedDepGraph = null;
    }

    @Override
    public ObligationType getObligationType() {
        return ObligationType.UNKNOWN;
    }

    public static ConfTRSProblem create(ImmutableSet<Rule> R) {
        return new ConfTRSProblem(R);
    }

    public static ConfTRSProblem create(ImmutableSet<Rule> R, HereditaryProperties m) {
        return new ConfTRSProblem(R, m);
    }

    private ConfTRSProblem(final ImmutableSet<Rule> rules, HereditaryProperties m) {
        this(rules);
        this.isLeftLinear = m.isLeftLinear();
        this.isLinear = m.isLinear();
        this.isNonOverlapping = m.isNonOverlapping();
    }

    private ConfTRSProblem(final ImmutableSet<Rule> rules,
                           CriticalPairs critPairs,
                           Integer maxArity,
                           Boolean nonOverlapping,
                           ImmutableSet<FunctionSymbol> defSymbolsOfR,
                           ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> ruleMap,
                           ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> reverseRuleMap) { // Added dps
        this(rules);

        this.critPairs = critPairs;
        this.maxArity = maxArity;
        this.isNonOverlapping = nonOverlapping;
        this.defSymbolsOfR = defSymbolsOfR;
        this.ruleMap = ruleMap;
        this.reverseRuleMap = reverseRuleMap;
    }

    public static ConfTRSProblem create(ImmutableSet<Rule> R,
                                        CriticalPairs critPairs,
                                        Integer maxArity,
                                        Boolean nonOverlapping,
                                        ImmutableSet<FunctionSymbol> defSymbolsOfR,
                                        ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> ruleMap,
                                        ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> reverseRuleMap) { // Added dps
        return new ConfTRSProblem(R,
                                  critPairs,
                                  maxArity,
                                  nonOverlapping,
                                  defSymbolsOfR,
                                  ruleMap,
                                  reverseRuleMap);
    }

    @Override
    public boolean equals(final Object oth) {
        if (this == oth) {
            return true;
        }

        if (oth == null) {
            return false;
        }

        if (oth.getClass() != this.getClass()) {
            return false;
        }

        final ConfTRSProblem other = (ConfTRSProblem) oth;
        return this.rules.equals(other.rules);
    }

    public YNM getTerminationResult() {
        return this.termination.getTruthValue().fallbackToYNM();
    }

    public HereditaryProperties getHereditaryProperties() {
        return new HereditaryProperties(this.isLeftLinear,
                                        this.isLinear,
                                        this.isNonOverlapping);
    }
    
    public QTRSProblem getInnermostTerminatingProblem() {
        if (this.innermostTermination == null) {
            synchronized (this) {
                if (this.innermostTermination == null) {
                    this.innermostTermination = QTRSProblem.create(this.getRules()).createInnermost();
                }
            }
        }
        return this.innermostTermination;
    }

    @Override
    public int hashCode() {
        return this.hashCode;
    }

    public ImmutableSet<Rule> getRules() {
        return this.rules;
    }

    public boolean isOrthogonal(Abortion aborter) {
        return this.isLeftLinear() && this.isNonOverlapping(aborter);
    }

    public boolean isLeftLinear() {
        if (this.isLeftLinear == null) {
            synchronized (this) {
                if (this.isLeftLinear == null) {
                    this.isLeftLinear = this.calculateLeftLinear();
                }
            }
        }
        return this.isLeftLinear;
    }

    private boolean calculateLeftLinear() {
        for (Rule rule : this.rules)
            if (!rule.getLeft().isLinear())
                return false;

        return true;
    }

    public boolean isLinear() {
        if (this.isLinear == null) {
            synchronized (this) {
                if (this.isLinear == null) {
                    this.isLinear = calculateLinearity();
                }
            }
        }
        return this.isLinear;
    }

    private boolean calculateLinearity() {
        if (this.isLeftLinear() == false)
            return false;

        for (Rule rule : this.rules)
            if (!rule.getRight().isLinear())
                return false;

        return true;
    }

    public boolean isNotLayerPreserving() {
        if (this.isNotLayerPreserving == null) {
            synchronized (this) {
                if (this.isNotLayerPreserving == null) {
                    this.isNotLayerPreserving = calculateNotLayerPreserving();
                }
            }
        }
        return this.isNotLayerPreserving;
    }

    private boolean calculateNotLayerPreserving() {
        if (this.isCollapsing()) {
            return true;
        }
        return this.getSharedLayerPreservingConstructorSymbols().size() == 0;
    }

    public CriticalPairs getCriticalPairs() {
        if (this.critPairs == null) {
            synchronized (this) {
                if (this.critPairs == null) {
                    this.critPairs = new CriticalPairs(this);
                }
            }
        }
        return this.critPairs;
    }

    public boolean isNonOverlapping(Abortion aborter) {
        if (this.isNonOverlapping == null) {
            synchronized (this) {
                if (this.isNonOverlapping == null) {
                    this.isNonOverlapping = this.getCriticalPairs().isNonOverlapping(aborter);
                }
            }
        }
        return this.isNonOverlapping;
    }

    /**
     * Saves a QTRS Problem from the Rule Set of the TRS. Future Results will link to the same TRS Problem.
     * @return QTRSProblem of same R
     */
    public QTRSProblem getQTRSProblem() {
        if (this.termination == null) {
            synchronized (this) {
                if (this.termination == null) {
                    this.termination = QTRSProblem.create(this.rules);
                }
            }
        }
        return this.termination;
    }

    public SimpleGraph<FunctionSymbol, Object> getFunctionSymbolDependencyGraph() {
        if (this.functionDependencyGraph == null) {
            synchronized (this) {
                if (this.functionDependencyGraph == null) {
                    this.calculateAndSetFSDG();
                }
            }
        }
        return this.functionDependencyGraph;
    }

    public Map<FunctionSymbol, Node<FunctionSymbol>> getFunctionSymbolDependencyGraphNodeMap() {
        if (this.functionDependencyGraphNodeMap == null) {
            synchronized (this) {
                if (this.functionDependencyGraph == null) {
                    this.calculateAndSetFSDG();
                }
            }
        }
        return this.functionDependencyGraphNodeMap;
    }
    
    public SimpleGraph<ImmutableLinkedHashSet<FunctionSymbol>, Void> getCondencedDepGraph() {
        if (this.condencedDepGraph == null) {
            synchronized (this) {
                if (this.condencedDepGraph == null) {
                    final SimpleGraph<FunctionSymbol, Object> graph = this.getFunctionSymbolDependencyGraph();
                    this.condencedDepGraph = graph.getCondensationGraph(true);
                }
            }
        }
        return this.condencedDepGraph;
    }

    private void calculateAndSetFSDG() {
        Pair<SimpleGraph<FunctionSymbol, Object>, Map<FunctionSymbol, Node<FunctionSymbol>>> pair =
                                                                                                  this.generateFunctionGraph();
        this.functionDependencyGraph = pair.x;
        this.functionDependencyGraphNodeMap = pair.y;
    }

    /**
     * Partitions the TRS R into disjoint sets of rules. This is done by building a
     * graph of the defined function symbols, where rules create edges. The
     * connected components of this symbol graph dictate the partitioning of the rules.
     * The result is cached for efficiency.
     * @return A list of disjoint sets of rules.
     */
    public Collection<ImmutableSet<Rule>> disjointRules() {
        final SimpleGraph<FunctionSymbol, Object> symbolGraph = this.getFunctionSymbolDependencyGraph();
        return symbolGraphToList(symbolGraph);
    }

    public Collection<ImmutableSet<Rule>> getConstructorSharingRules(boolean layerpreserving) {
        final SimpleGraph<FunctionSymbol, Object> graph =
                                                        this.filterConstructorNodes(this.getFunctionSymbolDependencyGraph(),
                                                                                    this.getFunctionSymbolDependencyGraphNodeMap(),
                                                                                    layerpreserving);
        return symbolGraphToList(graph);
    }
    
    public Collection<ImmutableSet<Rule>> calculateCompositableRules() {
        final SimpleGraph<ImmutableLinkedHashSet<FunctionSymbol>, Void> congraph = this.getCondencedDepGraph();
        final ImmutableSet<FunctionSymbol> nonLPF = this.getNonLayerPreservingConstructorSymbols();
        final Set<Set<ImmutableLinkedHashSet<FunctionSymbol>>> components = GraphAnalysis.findSourceInitiatedFlows(congraph,
                                                                                                                   F -> {
                                                                                                                       if (F.size() != 1) return false;
                                                                                                                       FunctionSymbol f = F.iterator().next();
                                                                                                                       return nonLPF.contains(f);
                                                                                                                       }
                                                                                                                   );
        
        final Set<Set<FunctionSymbol>> sets = components.stream()
            .map( ssc -> ssc.stream().flatMap(Set::stream).collect(Collectors.toSet()))
            .collect(Collectors.toSet());
        

        return this.setsOfFunctionSymbolSetToListOfRules(sets);
    }

    /**
     * generates an undirected graph that connects all nodes to all other nodes which
     * are present in any subterm of the left or righthand side
     * @return
     */
    private Pair<SimpleGraph<FunctionSymbol, Object>, Map<FunctionSymbol, Node<FunctionSymbol>>>
            generateFunctionGraph() {
        final ImmutableSet<FunctionSymbol> allSymbols = this.getSignature();
        final Map<FunctionSymbol, Node<FunctionSymbol>> symbolToNodeMap = new HashMap<>();
        final SimpleGraph<FunctionSymbol, Object> symbolGraph = new SimpleGraph<>();

        // create node for every symbol
        for (final FunctionSymbol symbol : allSymbols) {
            final Node<FunctionSymbol> n = new Node<>(symbol);
            symbolGraph.addNode(n);
            symbolToNodeMap.put(symbol, n);
        }

        for (final Rule rule : this.rules) {
            final FunctionSymbol lhsRootSymbol = rule.getRootSymbol();
            final Node<FunctionSymbol> lhsRootNode = symbolToNodeMap.get(lhsRootSymbol);

            if (lhsRootNode == null) {
                continue;
            }

            final Set<FunctionSymbol> otherSymbols = new HashSet<>();
            otherSymbols.addAll(rule.getLeft().getFunctionSymbols());
            otherSymbols.addAll(rule.getRight().getFunctionSymbols());

            for (final FunctionSymbol otherSymbol : otherSymbols) {

                final Node<FunctionSymbol> otherNode = symbolToNodeMap.get(otherSymbol);
                if (otherNode != null) {
                    symbolGraph.addEdge(lhsRootNode, otherNode);
                }
            }
        }
        
        return new Pair<SimpleGraph<FunctionSymbol, Object>, Map<FunctionSymbol, Node<FunctionSymbol>>>(symbolGraph,
                                                                                                        symbolToNodeMap);
    }


    public ImmutableSet<FunctionSymbol> getSharedConstructorSymbols() {
        if (this.sharedConstructorSymbols == null) {
            synchronized (this) {
                if (this.sharedConstructorSymbols == null) {
                    final ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> ruleMap = this.getRuleMap();
                    final SimpleGraph<ImmutableLinkedHashSet<FunctionSymbol>, Void>
                        conGraph = this.getCondencedDepGraph();
                    final Set<FunctionSymbol> nonDependentDependencies = conGraph.getNodes().stream()
                            .filter(n -> conGraph.getOut(n).size() == 0)
                            .filter(n -> conGraph.getIn(n).size() >= 2)
                            .map(Node::getObject)
                            .flatMap(Set::stream)
                            .collect(Collectors.toSet());
                    
                    Set<FunctionSymbol> constructorSymbols = this.getSignature()
                                                                 .stream()
                                                                 .filter(x -> ruleMap.get(x) == null)
                                                                 .filter(f -> nonDependentDependencies.contains(f)) // only constructor symbols which even could be shared
                                                                 .collect(Collectors.toSet());
                    this.sharedConstructorSymbols = ImmutableCreator.create(constructorSymbols);
                }
            }
        }
        return this.sharedConstructorSymbols;
    }
    
    public ImmutableSet<FunctionSymbol> getSharedLayerPreservingConstructorSymbols(){
        if (this.sharedLayerPreservingConstructorSymbols == null) {
            synchronized(this) {
                if (this.sharedLayerPreservingConstructorSymbols == null) {
                    this.sharedLayerPreservingConstructorSymbols = this.calculateSharedLayerPreservingConstructorSymbols();
                }
            }
        }
        return this.sharedLayerPreservingConstructorSymbols;
    }
    
    private ImmutableSet<FunctionSymbol> calculateSharedLayerPreservingConstructorSymbols(){
        if (this.isCollapsing()) {
            return EMPTYFSET;
        }
        ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> invRuleMap = this.getReverseRuleMap();
        Set<FunctionSymbol> lpConstructorSymbols = this.getSharedConstructorSymbols()
                .stream()
                .filter(f -> {
                    ImmutableSet<Rule> r = invRuleMap.get(f);
                    if(r == null) return true;
                    return invRuleMap.get(f).size() == 0;
                })
                .collect(Collectors.toSet());
       return ImmutableCreator.create(lpConstructorSymbols);
    }
    
    
    public ImmutableSet<FunctionSymbol> getNonLayerPreservingConstructorSymbols(){
        if (this.nonLayerPreservingConstructorSymbols == null) {
            synchronized(this) {
                if (this.nonLayerPreservingConstructorSymbols == null) {
                    Set<FunctionSymbol> lpConstructorFunctionSymbols = this.getSharedLayerPreservingConstructorSymbols();
                    Set<FunctionSymbol> set = this.getSharedConstructorSymbols().stream()
                            .filter(f -> !lpConstructorFunctionSymbols.contains(f))
                            .collect(Collectors.toSet());
                    this.nonLayerPreservingConstructorSymbols = ImmutableCreator.create(set);
                }
            }
        }
        return this.nonLayerPreservingConstructorSymbols;
    }
    

    /**
     * Generates a Copy of G, 
     * @param graph
     * @param symbolToNodeMap
     * @return copy graph without shared construction symbols
     */
    private SimpleGraph<FunctionSymbol, Object> filterConstructorNodes(final SimpleGraph<FunctionSymbol, Object> g,
                                                                       Map<FunctionSymbol, Node<FunctionSymbol>> symbolToNodeMap,
                                                                       boolean layerpreserving) {
        Collection<FunctionSymbol> constructorSymbols = layerpreserving ? this.getSharedLayerPreservingConstructorSymbols() : this.getSharedConstructorSymbols();
        SimpleGraph<FunctionSymbol, Object> gn = g.getCopy();
        constructorSymbols
            .stream()
            .map(x -> symbolToNodeMap.get(x))
            .forEach(x -> gn.removeNode(x));;
        return gn;

    }

    /**
     * Gets all the associated rules from all isolated subgraph and their function symbols.
     * @param symbolGraph
     * @return
     */
    private Collection<ImmutableSet<Rule>> symbolGraphToList(final SimpleGraph<FunctionSymbol, Object> symbolGraph) {

        final Set<Set<FunctionSymbol>> symbolComponents = symbolGraph.getWCCs().stream()
                .map(wcc -> wcc.stream().map(Node::getObject).collect(Collectors.toSet()))
                .collect(Collectors.toSet());

        return this.setsOfFunctionSymbolSetToListOfRules(symbolComponents);
    }
    
    private Collection<ImmutableSet<Rule>> setsOfFunctionSymbolSetToListOfRules(final Set<Set<FunctionSymbol>> symbolComponents) {
        final Collection<ImmutableSet<Rule>> result = new ArrayList<>();
        
        for (final Set<FunctionSymbol> component : symbolComponents) {
            LinkedHashSet<Rule> rules = component.stream()
                    .map(getRuleMap()::get)
                    .filter(Objects::nonNull)
                    .flatMap(Set::stream)
                    .collect(Collectors.toCollection(LinkedHashSet<Rule>::new));
            if(!rules.isEmpty()) {
                result.add(ImmutableCreator.create(rules));
            }
        }
        return result;
    }

    private void calculateDefSymbolsAndRuleMap() {
        final Map<FunctionSymbol, Set<Rule>> ruleMap = new LinkedHashMap<FunctionSymbol, Set<Rule>>();
        for (final Rule rule : this.rules) {
            final FunctionSymbol f = rule.getRootSymbol();
            Set<Rule> fRules = ruleMap.get(f);
            if (fRules == null) {
                fRules = new LinkedHashSet<Rule>();
                ruleMap.put(f, fRules);
            }
            fRules.add(rule);
        }
        // make immutable
        final Map<FunctionSymbol, ImmutableSet<Rule>> immutableMap =
                                                                   new LinkedHashMap<FunctionSymbol, ImmutableSet<Rule>>();
        for (final Map.Entry<FunctionSymbol, Set<Rule>> entry : ruleMap.entrySet()) {
            immutableMap.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
        }
        this.ruleMap = ImmutableCreator.create(immutableMap);
        this.defSymbolsOfR = ImmutableCreator.create(immutableMap.keySet());
    }

    /**
     * get R as a mapping from defined symbols to corresponding rules
     */
    public ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> getRuleMap() {
        if (this.ruleMap == null) {
            synchronized (this) {
                if (this.ruleMap == null) {
                    this.calculateDefSymbolsAndRuleMap();
                }
            }
        }
        return this.ruleMap;
    }

    private void calculateReverseRuleMap() {
        final Map<FunctionSymbol, Set<Rule>> reverseRuleMap = Rule.getReversedRuleMap(this.rules);
        final Map<FunctionSymbol, ImmutableSet<Rule>> immutableMap =
                                                                   new LinkedHashMap<FunctionSymbol, ImmutableSet<Rule>>();
        for (final Map.Entry<FunctionSymbol, Set<Rule>> entry : reverseRuleMap.entrySet()) {
            immutableMap.put(entry.getKey(), ImmutableCreator.create(entry.getValue()));
        }
        this.reverseRuleMap = ImmutableCreator.create(immutableMap);
    }

    /**
     * returns whether R has at least one collapsing rule;
     * @return
     */
    public boolean isCollapsing() {
        return this.getReverseRuleMap().containsKey(null);
    }

    /**
     * get R^{-1} as a mapping from function symbols of rhs to corresponding rules.
     * Note that the rules a still from left to right, i.e. one has to read the rules
     * reversed!
     */
    public ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> getReverseRuleMap() {
        if (this.reverseRuleMap == null) {
            synchronized (this) {
                if (this.reverseRuleMap == null) {
                    this.calculateReverseRuleMap();
                }
            }
        }
        return this.reverseRuleMap;
    }

    @SuppressWarnings("unused")
    private final static ImmutableSet<Rule> EMPTYSET = ImmutableCreator.create(java.util.Collections.<Rule> emptySet());
    
    private final static ImmutableSet<FunctionSymbol> EMPTYFSET = ImmutableCreator.create(java.util.Collections.<FunctionSymbol> emptySet());

    public ImmutableSet<FunctionSymbol> getDefinedSymbolsOfR() {
        return this.defSymbolsOfR;
    }

    public ImmutableSet<FunctionSymbol> getSignature() {
        return this.signature;
    }

    /**
     * looksup a tuple symbol for a defined symbol f. If it is not defined, a new symbol is created (which is not
     * contained in allSyms) and the mapping is stored, and the new symbol is added to allSyms
     * @param f
     * @param defToTup
     * @param allSyms
     * @return
     */
    //TODO: Change this place to a different more suitable place/class
    public static FunctionSymbol getTupleSymbol(final FunctionSymbol f,
                                                final Map<FunctionSymbol, FunctionSymbol> defToTup,
                                                final Set<FunctionSymbol> allSyms) {
        FunctionSymbol tf = defToTup.get(f);
        if (tf == null) {
            final String wishedName = f.getName().toUpperCase();
            final int arity = f.getArity();
            int nr = 1;
            tf = FunctionSymbol.create(wishedName, arity);
            while (!allSyms.add(tf)) {
                tf = FunctionSymbol.create(wishedName + "^" + nr, arity);
                nr++;
            }

            defToTup.put(f, tf);
        }
        return tf;
    }

    /**
     * @return Maximal arity of signature
     */
    public int getMaxArity() {
        if (this.maxArity == null) {
            int max = 0;
            for (final FunctionSymbol fs : this.getSignature()) {
                final int arity = fs.getArity();
                if (arity > max) {
                    max = arity;
                }
            }
            this.maxArity = max;
        }
        return this.maxArity;
    }

    /**
     * returns the set of terms in R
     */
    @Override
    public Set<TRSTerm> getTerms() {
        final Set<TRSTerm> terms = CollectionUtils.getTerms(this.rules);
        return terms;
    }

    @Override
    public String export(final Export_Util o) {
        final StringBuilder s = new StringBuilder();
        s.append(o.export("Confluence TRS"));
        s.append(o.cond_linebreak());
        if (this.rules.isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS R consists of the following rules:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.rules, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        s.append(o.linebreak());

        return s.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }

    @Override
    public String toHTML() {
        return this.export(new HTML_Util());
    }

    @Override
    public String toExternString() {
        final TRSGenerator trsGen = new TRSGenerator();
        trsGen.writeRules(this.rules);
        return trsGen.getTRSString(false, null);
    }

    @Override
    public String externName() {
        return "conf_trs";
    }

    public boolean isRightGround() {
        for (final Rule rule : this.getRules()) {
            if (!rule.getRight().getVariables().isEmpty()) {
                return false;
            }
        }
        return true;
    }

    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element e = XMLTag.QTRS_OBL.createElement(doc);
        final Element f = XMLTag.QTRS.createElement(doc);

        final Element trs = XMLTag.TRS.createElement(doc);
        CollectionUtils.addChildren(this.rules, trs, doc, xmlMetaData);
        f.appendChild(trs);

        final Element sig = XMLTag.SIGNATURE.createElement(doc);
        CollectionUtils.addChildren(this.getSignature(), sig, doc, xmlMetaData);
        f.appendChild(sig);

        e.appendChild(f);
        return e;
    }

    @Override
    public Element getCPFInput(final Document doc, final XMLMetaData xmlMetaData, final TruthValue tv) {
        final Element trsInput = CPFTag.TRS_INPUT.create(doc,
                                                         CPFTag.trs(doc, xmlMetaData, this.getRules()));

        final Element strategy = CPFTag.STRATEGY.createElement(doc);

        return trsInput;
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "Confluence for TRS");
    }

    /**
     * {@inheritDoc}
     */
    @Override
    public String getStrategyName() {
        return "conf_trs";
    }

    /* (non-Javadoc)
     * @see aprove.ProofTree.Obligations.BasicObligation.DefaultBasicObligation#offersCertifiableTechniques()
     */
    @Override
    public boolean offersCertifiableTechniques() {
        return false;
    }
}
