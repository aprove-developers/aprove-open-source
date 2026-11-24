package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.exit.*;
import aprove.input.*;
import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPConstraints.SolutionIterator.*;
import aprove.verification.dpframework.Orders.Utility.GPOLO.*;
import aprove.verification.oldframework.Algebra.GeneralPolynomials.Coefficients.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * The InductionCalculus generates the implication(constraints)
 * for each DP in a given QDPProblem
 *
 * therefore it is an InfRuleContext
 * so it can provide some global information about the QDPProblem to some InfRule
 * which are applied to the constraints within the calculation process.
 *
 * @author swiste, mpluecke
 */
public abstract class AbstractInductionCalculus<C extends GPolyCoeff> implements InfRuleContext<C> {
    protected boolean initialized = false;
    protected Options options;
    int ruleCounter; // All InfRules within this InductionCalculus get thier identification number
    protected int varCounter; // each new variable get
    protected StrategyLevel[] leveledStrategy; // all over strategy
    InfRule lastRule; // last applied rule
    TRSVisitable lastTop; // Constraint for which all rules in current level are checked for application
    Map<TRSVariable, Integer> countMap; // cache for variable occurence
    private Set<FunctionSymbol> definedSymbols; // defined symbols of current QDPProblem
    Map<FunctionSymbol, ImmutableSet<GeneralizedRule>> ruleMap; // mapping from defined symbols to rules
    protected Set<FunctionSymbol> constructorSymbols; // constructor symbols of current QDPProblem
    Set<FunctionSymbol> constructorNoHeadSymbols; // constructor symbols of current QDPProblem
    Set<FunctionSymbol> nonRecursiveSymbols; // non-recursive symbols of current QDPProblem
    Set<FunctionSymbol> tailRecursiveSymbols; // tail-recursive symbols of current QDPProblem
    InductionCalculusProof proof; // proof
    Exportable lastMark; // each rule can explizit export an object to the proof for further information
    Abortion aborter; // the standard aborter
    protected final GInterpretation<C> polyInterpretation; // poly interpretation to switch from terms to polys
    protected final FreshNameGenerator freshVarsGenerator;

    protected InfRule5Induction infRule5Induction = new InfRule5Induction();

    public final StrategyLevel startStrategy = new StrategyLevel("startStrategy", new InfRule[] {
    /* 1*/new InfRule12LeftCons(),
    /* 2*/new InfRule4DeleteA(), new InfRule3LeftVariableA(), new InfRule6SimplifyConditionA(),

    /* 3*/new InfRule3LeftConsRightVariableD(),

    /* 4*/new InfRule3LeftVariableB(),

    /* 5*/new InfRule8FuncVar(), }, true);

    public final StrategyLevel preFinalStrategy = new StrategyLevel("preFinalStrategy", new InfRule[] {
        /* 7*/new InfRule12LeftCons(),
        new InfRule3LeftVariableC(),
        new InfRule6SimplifyConditionB(),
        new InfRule3LeftConsRightVariableE(),
        /* 8*/new InfRule4DeleteC(),

    }, true);

    public final StrategyLevel finalStrategy = new StrategyLevel("finalStrategy", new InfRule[] {
    /* 8*/new InfRule4DeleteD() }, true);

    public final StrategyLevel standardStrategy = new StrategyLevel("standardStrategy", new InfRule[] {
        /* 1*/new InfRule12LeftCons(),
        new InfRule3LeftVariableA(),
        new InfRule6SimplifyConditionA(),
        new InfRule4DeleteA(),
        new InfRule3LeftConsRightVariableD(),
        /* 4*/new InfRule3LeftVariableB(),
        /* 5*/new InfRule8FuncVar(),
        /* 6*/new InfRule4DeleteB(),
        new InfRule4DeleteE(),
        // new InfRule9ReverseSubstitution(), //////////////////// !!!!!!!!!!!!!!!!!!!!!!!!
        this.infRule5Induction, }, true);

    /**
     * test for debugging
     */
    public static void main(final String argv[]) {
        try {
            doMain();
        } catch (KillAproveException e) {
            e.runSystemExit();
        }
    }

    private static void doMain() throws KillAproveException {
        final Map<String, TRSVariable> vars = EasyInput.parseVariables("u,v,x,y,z");
        //      Constraint a = EasyInput.parseConstraint(vars, "imp(no,&(>(f(a,b),c)),&(>(f(a,b),d),>(f(b,a),c)))");
        //      Constraint b = EasyInput.parseConstraint(vars, "imp(no,&(>(f(x,y),c),>(f(y,z),c)),>(f(z,y),c))");
        //       Constraint a = EasyInput.parseConstraint(vars, "&(>(f(a,b),c))");
        //        Constraint b = EasyInput.parseConstraint(vars, "&(>(f(x,b),c),>(f(a,y),c))");
        final Constraint a = EasyInput.parseConstraint(vars, ">(f(a,b),c)");
        final Constraint b = EasyInput.parseConstraint(vars, "&(>(f(x,b),c),>(f(a,y),c))");
        final Set<FunctionSymbol> fs = new LinkedHashSet<FunctionSymbol>();
        fs.add(FunctionSymbol.create("a", 0));
        fs.add(FunctionSymbol.create("b", 0));
        final SolutionIterator soli =
            SolutionIterator.create(Direction.right, a, b, new SolutionConstraints(fs, false), null);
        final Solution sol = new Solution(new LinkedHashSet<>(vars.values()));
        TRSSubstitution subs = null;
        do {
            sol.reset();
            if (soli.extendWithCurrent(sol)) {
                subs = sol.getSubstitution();
                System.out.println(subs);
            }
            System.out.println(sol.isValid());
        } while (!soli.next());
        throw new KillAproveException(1);
    }

    /**
     * Standard constructor
     * @param proof    // a proof where the simplification steps are protocolled
     * @param options  // options
     * @param aborter  // standard aborter
     */
    public AbstractInductionCalculus(
        final InductionCalculusProof proof,
        final Options options,
        final GInterpretation<C> polyInterpretation,
        final Abortion aborter)
    {
        super();
        this.proof = proof;
        this.options = options;
        this.aborter = aborter;
        this.polyInterpretation = polyInterpretation;
        this.freshVarsGenerator = new FreshNameGenerator(FreshNameGenerator.PROLOG_VARS);
        //test();
    }

    protected void init() {
        this.initialized = true;
        this.leveledStrategy = this.initLeveledStrategy();
        this.lastTop = null;
        this.countMap = null;
        this.varCounter = 0;
        this.ruleCounter = 0;
        this.constructorSymbols = this.createConstructorSymbols();
        this.definedSymbols = this.createDefinedRSymbols();
        this.constructorNoHeadSymbols = this.createNoHeadSymbols();
        this.ruleMap = this.createRuleMap();
        this.nonRecursiveSymbols = new LinkedHashSet<FunctionSymbol>();
        for (final FunctionSymbol f : this.definedSymbols) {
            if (!AbstractInductionCalculus.isRecursive(f, this.ruleMap)) {
                this.nonRecursiveSymbols.add(f);
            }
        }
        this.tailRecursiveSymbols = new LinkedHashSet<FunctionSymbol>(this.definedSymbols);
        this.tailRecursiveSymbols.removeAll(this.nonRecursiveSymbols);
        final Iterator<FunctionSymbol> itf = this.tailRecursiveSymbols.iterator();
        while (itf.hasNext()) {
            final FunctionSymbol f = itf.next();
            if (!AbstractInductionCalculus.isTailRecursive(f, this.ruleMap.get(f), this.definedSymbols)) {
                itf.remove();
            }
        }
        for (final StrategyLevel level : this.leveledStrategy) {
            if (level != null) {
                for (final InfRule ir : level.getStrategy()) {
                    ir.initContext(this);
                }
            }
        }
    }

    /**
     * @param f
     * @param rules of f
     * @param definedSymbols
     * @return true iff f is tail recursive
     *
     * My tail recursive definition (not exact tail recursive):
     * f tail recursive iff f is recursive and in each right side of a rule of f,
     * f occurs only at root position or it does not occur
     * and the root symbol is no defined symbol
     */
    private static boolean isTailRecursive(
        final FunctionSymbol f,
        final Set<GeneralizedRule> rules,
        final Set<FunctionSymbol> definedSymbols)
    {
        for (final GeneralizedRule r : rules) {
            if (!r.getRight().isVariable()) {
                final TRSFunctionApplication fa = (TRSFunctionApplication) r.getRight();
                final FunctionSymbol far = fa.getRootSymbol();
                if (definedSymbols.contains(far) && !far.equals(f)) {
                    return false;
                }
                for (final TRSTerm t : fa.getArguments()) {
                    if (t.getFunctionSymbols().contains(f)) {
                        return false;
                    }
                }
            }
        }
        return true;
    }

    /**
     * add to target all function symbols the function symbol f depends on by using a given rule map
     * @param f
     * @param target
     * @param ruleMap
     */
    private static void addDependees(
        final FunctionSymbol f,
        final Set<FunctionSymbol> target,
        final Map<FunctionSymbol, ImmutableSet<GeneralizedRule>> ruleMap)
    {
        final Set<GeneralizedRule> rs = ruleMap.get(f);
        if (rs == null) {
            return;
        }
        for (final GeneralizedRule r : rs) {
            target.addAll(r.getRight().getFunctionSymbols());
        }
    }

    /**
     * @param f
     * @param ruleMap
     * @return true iff f is recursive
     */
    private static boolean isRecursive(
        final FunctionSymbol f,
        final Map<FunctionSymbol, ImmutableSet<GeneralizedRule>> ruleMap)
    {
        final Set<FunctionSymbol> ready = new LinkedHashSet<FunctionSymbol>();
        final Set<FunctionSymbol> toDo = new LinkedHashSet<FunctionSymbol>();
        AbstractInductionCalculus.addDependees(f, toDo, ruleMap);
        while (!toDo.isEmpty()) {
            final FunctionSymbol g = toDo.iterator().next();
            toDo.remove(g);
            if (!ready.contains(g)) {
                if (f.equals(g)) {
                    return true;
                }
                AbstractInductionCalculus.addDependees(g, toDo, ruleMap);
                ready.add(g);
            }
        }
        return false;
    }

    @Override
    public Set<FunctionSymbol> getConstructorNoHeadSymbols() {
        return this.constructorNoHeadSymbols;
    }

    @Override
    public boolean isNonRecursive(final FunctionSymbol f) {
        return this.nonRecursiveSymbols.contains(f);
    }

    @Override
    public boolean isTailRecursive(final FunctionSymbol f) {
        return this.tailRecursiveSymbols.contains(f);
    }

    public Set<FunctionSymbol> getConstructorSymbols() {
        return this.constructorSymbols;
    }

    @Override
    public boolean isDefinedSymbol(final FunctionSymbol f) {
        return this.definedSymbols.contains(f);
    }

    @Override
    public GInterpretation<C> getPolyInterpretation() {
        return this.polyInterpretation;
    }

    /**
     * @return true iff a variable occurs only once or never in the lastTop implication
     */
    @Override
    public boolean occursOnce(final TRSVariable v) {
        if (this.countMap == null) {
            this.countMap = this.lastTop.getVariableCount();
        }
        final Integer i = this.countMap.get(v);
        return (i != null) && (i == 1);
    }

    /**
     * @return true iff a variable occurs only n times or never in the lastTop implication
     */
    @Override
    public boolean occursNTimes(final TRSVariable v, final int n) {
        if (this.countMap == null) {
            this.countMap = this.lastTop.getVariableCount();
        }
        final Integer i = this.countMap.get(v);
        return (i != null) && (i == n);
    }

    /**
     * some InfRules could set thier mark for extra informations in proof output
     */
    @Override
    public void setMark(final Exportable mark) {
        this.lastMark = mark;
    }

    /**
     * some InfRules could set thier mark for extra informations in proof output
     */
    public Exportable getMark() {
        return this.lastMark;
    }

    /**
     * the rewritingCounter parameter
     */
    @Override
    public int getRewritingCount() {
        return this.options.rewritingCounter;
    }

    /**
     * the inductionCounter parameter
     */
    @Override
    public int getInductionCount() {
        return this.options.inductionCounter;
    }

    /**
     * Marker used to block induction for a constraint
     */
    @Override
    public Object getInductionBlockId() {
        return this;
    }

    /**
     * return the next free rule number
     */
    @Override
    public int getNextRuleNumber() {
        this.ruleCounter++;
        return this.ruleCounter - 1;
    }

    /**
     * the count of rules all over used in this InductionCalculus
     */
    @Override
    public int getRuleCount() {
        return this.ruleCounter;
    }

    /**
     * rules of the QDPProblem for function symbol f
     */
    @Override
    public Set<? extends GeneralizedRule> getRulesFor(final FunctionSymbol f) {
        return this.ruleMap.get(f);
    }

    /**
     * creates and returns a new fresh variable in context of this InductionCalculus
     */
    @Override
    public TRSVariable getFreshVariable() {
        final TRSVariable v = TRSTerm.createVariable(this.freshVarsGenerator.getFreshName("x" + this.varCounter, false));
        this.varCounter++;
        return v;
    }

    @Override
    public TRSVariable getFreshVariable(final TRSVariable replace) {
        final String newName = this.freshVarsGenerator.getFreshName(replace.getName(), false);
        if (!newName.equals(replace.getName())) {
            return TRSTerm.createVariable(newName);
        }
        return replace;
    }

    /* mpluecker: REMOVE, variable clashs possible
    public Variable getFreshVariable(){
        // FIXME: This is dangerous....
        Variable v = Term.createVariable("x"+this.varCounter);
        this.varCounter++;
        return v;
    }*


    /**
     * creates and returns a new fresh variables in context of this InductionCalculus
     */
    @Override
    public List<TRSVariable> getFreshVariables(final int count) {
        final List<TRSVariable> fvars = new LinkedList<TRSVariable>();
        for (int i = count - 1; i >= 0; i--) {
            fvars.add(this.getFreshVariable());
        }
        return fvars;
    }

    /**
     * creates and returns a renaming substitution for the variables vars in fresh variables
     */
    @Override
    public TRSSubstitution getFreshRenamingFor(final Collection<TRSVariable> vars) {
        final Map<TRSVariable, TRSTerm> map = new LinkedHashMap<TRSVariable, TRSTerm>();
        final Iterator<TRSVariable> itv = vars.iterator();
        for (final TRSVariable nv : this.getFreshVariables(vars.size())) {
            map.put(itv.next(), nv);
        }
        return TRSSubstitution.create(ImmutableCreator.create(map));
    }

    /**
     * checks if a function application has pairwise different variables as arguments
     * returns this variables or null if thier are not pairwise different
     */
    @Override
    public List<TRSVariable> getPDVaribales(final TRSFunctionApplication fal) {
        final List<? extends TRSTerm> args = fal.getArguments();
        for (final TRSTerm t : fal.getArguments()) {
            if (!t.isVariable()) {
                return null;
            }
        }
        return fal.getVariables().size() == args.size() ? (List<TRSVariable>) args : null;
    }

    /**
     * count up an inverse lexicographic combination counter represented as array, were the position 'ignore' is ignored
     */
    protected static boolean inc(final int[] counter, final int overflow, final int ignore) {
        for (int i = 0; i < counter.length; i++) {
            if (ignore != i) {
                counter[i]++;
                if (counter[i] == overflow) {
                    counter[i] = 0;
                } else {
                    return true;
                }
            }
        }
        return false;
    }

    /**
     * Tries to apply each InfRule of a given level to an implication
     * if on rule is applicable thier result is returned, otherwise null
     * @param level InfRules which should be applied to the given implication
     * @param imp
     * @return the result of the application of the first applicable rule of the given level and the index of the rule, otherwise null
     * @throws AbortionException
     **/
    public Triple<Constraint, InfProofStepInfo, Integer> applyFirstRule(
        final StrategyLevel level,
        final Implication imp,
        final int startIndex) throws AbortionException
    {
        final InfRule[] strategy = level.getStrategy();
        for (int i = startIndex; i < strategy.length; i++) {
            this.lastRule = strategy[i];
            this.lastTop = imp;
            this.countMap = null;
            this.aborter.checkAbortion();
            // System.out.println("==========================================================================================>"+this.lastRule.getClass().getSimpleName());
            final Pair<Constraint, InfProofStepInfo> res = this.lastRule.applyToImplication(imp, this.aborter);
            if (res != null && res.x != imp) {
                // System.out.println("Success: "+this.lastRule.getClass().getSimpleName());
                return new Triple<Constraint, InfProofStepInfo, Integer>(res.x, res.y, i);
            }
        }
        return null;
    }

    /**
     * simplifies a list of implications (will be modified) by trying to apply the InfRules in the given level
     * @param level InfRules to try
     * @param cs list of implication (it is modified afterwards)
     * @throws AbortionException
     */
    public void levelSimplify(final StrategyLevel level, final List<Implication> cs) throws AbortionException {
        int readyCounter = 0;
        //System.out.println("SIMPLIFY: " + level);
        // show(cs);
        level.prepare(cs, this.proof, this.aborter);
        int toSize = cs.size();
        while (readyCounter < toSize) {
            Triple<Constraint, InfProofStepInfo, Integer> res;
            int lastRule = 0;
            do {
                final Implication current = cs.get(readyCounter);
                res = this.applyFirstRule(level, current, lastRule);
                if (res != null && res.x != current) {
                    this.proof.appliedRule(
                        current,
                        this.lastRule,
                        new LinkedList<Implication>(cs),
                        this.lastMark,
                        res.y,
                        readyCounter);
                    // System.out.println("==========================================================================================>"+this.lastRule.getClass().getSimpleName());
                    if (res.x.isConstraintSet()) {
                        cs.remove(readyCounter);
                        // TODO fixed position only used for debugging
                        cs.addAll(readyCounter, (Set) res.x);
                    } else {
                        cs.set(readyCounter, (Implication) res.x);
                    }
                    if (level.isRepeat()) {
                        lastRule = 0;
                        toSize = cs.size();
                    } else {
                        lastRule = res.z + 1;
                    }
                    // show(cs);
                    //System.out.println("!!!");
                } else {
                }
                if (this.aborter != null) {
                    this.aborter.checkAbortion();
                }
            } while (res != null && readyCounter < toSize);
            readyCounter++;
        }
    }

    /**
     * simplifies a list of implications
     * @param cs list of implication (it is modified afterwards)
     * @throws AbortionException
     */
    public void simplify(final List<Implication> cs) throws AbortionException {
        for (final Implication impl : cs) {
            for (final TRSVariable var : impl.getAllVars()) {
                this.freshVarsGenerator.lockName(var.getName());
            }
        }
        if (!this.initialized) {
            this.init();
        }
        int i = 0;
        for (final StrategyLevel level : this.leveledStrategy) {
            // System.out.println("Level: " + level + " - size " + cs.size());
            // show(cs);
            if (level == null) {
                this.reduce(cs);
            } else {
                this.levelSimplify(level, cs);
            }
            i++;
        }
        // System.out.println("Finished Level: " + leveledStrategy[leveledStrategy.length-1] + " - size " + cs.size());
        // show(cs);
    }

    /**
     * Simplifies the implications(constraints) for some pairs
     * @param map a map from Pair to a map from chains to list of implications (the constraints for each pair)
     * @throws AbortionException
     */
    public void simplify(final Map<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>> map)
        throws AbortionException
    {
        if (!this.initialized) {
            this.init();
        }
        for (final Map.Entry<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>> e : map.entrySet()) {
            for (final List<Implication> cs : e.getValue().values()) {
                for (final Implication impl : cs) {
                    for (final TRSVariable var : impl.getAllVars()) {
                        this.freshVarsGenerator.lockName(var.getName());
                    }
                }
            }
        }

        for (final Map.Entry<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>> e : map.entrySet()) {
            //            System.out.println("=================");
            //            System.out.println("Constraints for Pair " + e.getKey() + " reduced with these steps:");
            //            System.out.println(e.getValue());
            this.proof.forPairTheFollowingChainsWhereCreated(e.getKey());
            for (final Map.Entry<List<GeneralizedRule>, List<Implication>> impsRs : e.getValue().entrySet()) {
                //                System.out.println("   Sub Combination "
                //                    + e.getKey()
                //                    + "::"
                //                    + impsRs.getKey()
                //                    + " reduced with these steps:");
                this.proof.forChainTheFollowingConstrainsWhereCreated(impsRs.getKey());
                // show(impsRs.getValue());
                this.simplify(impsRs.getValue());
                this.proof.resultForChain(impsRs.getValue());
            }
            this.proof.resultForPair();
            //            System.out.println("=================");
        }
    }

    /**
     * Simplifies a list of implications(constraints) by erasing of equvivalent implication
     * @param cs
     */
    public void reduce(final List<Implication> cs) {
        final ConstraintComparator comparator = new ConstraintComparator();
        final List<Implication> ncs = new ArrayList<Implication>();
        nextConstraint:
        for (final Implication candidate : cs) {
            for (final Implication retained : ncs) {
                if (comparator.isRenamingOf(candidate, retained)) {
                    continue nextConstraint;
                }
            }
            ncs.add(candidate);
        }
        cs.clear();
        cs.addAll(ncs);
    }

    /**
     * show for debugging
     * @param cs
     */
    @Override
    public void show(final List<Implication> cs) {
        for (final Implication imp : cs) {
            System.out.println(">>  " + imp);
        }
    }

    /**
     * show for debugging
     * @param map
     */
    public void showMap(final Map<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>> map) {
        for (final Map.Entry<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>> e : map.entrySet()) {
            System.out.println(e.getKey() + ":  ");
            for (final Map.Entry<List<GeneralizedRule>, List<Implication>> rsImps : e.getValue().entrySet()) {
                System.out.println("  " + rsImps.getKey() + ":  ");
                this.show(rsImps.getValue());
                System.out.println();
            }
        }
    }

    /**
     * Simplifies the initial implications(constraints) for each chain of a pair
     * @return the map of simplicated implications(constraints) for each chain of a pair
     * @throws AbortionException
     */
    public Map<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>> simplify() throws AbortionException {
        if (!this.initialized) {
            this.init();
        }
        final Map<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>> map = this.createConstraintSetProRule();
        //        showMap(map);
        //        long l = System.currentTimeMillis();
        this.simplify(map);
        //        long z = System.currentTimeMillis();
        /*
        int i=0;
        System.out.println("tails: "+this.tailRecursiveSymbols);
        System.out.println("defined: "+this.definedSymbols);
        System.out.println("nonRec: "+this.nonRecursiveSymbols);
        System.out.println("Options: "+options);
        for (long t : leveltime){
            System.out.println("Time (ms)"+i+": "+t);
            i++;
        }
        System.out.println("Time (ms): "+(z-l)+"  Solution:");
        showMap(map);
        show(nmap);
        System.out.println("----");
        */

        return map;
    }

    @Override
    public String toString() {
        return "*";
    }

    public ConstraintsCache generateConstraintsCache() throws AbortionException {
        return new ConstraintsCache(
            new Pair<Map<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>>, InductionCalculusProof>(
                this.simplify(),
                this.proof), this.options, this.infRule5Induction.getAppliedInductions());
    }

    public static class Options {
        
        public final int hashCode;
        
        public final int leftChainCounter;
        public final int rightChainCounter;
        public final int inductionCounter;
        public final int rewritingCounter;

        public Options(
            final int leftChainCounter,
            final int rightChainCounter,
            final int inductionCounter,
            final int rewritingCounter)
        {
            this.leftChainCounter = leftChainCounter;
            this.rightChainCounter = rightChainCounter;
            this.inductionCounter = inductionCounter;
            this.rewritingCounter = rewritingCounter;
            
            this.hashCode = this.leftChainCounter * 6151 + this.rightChainCounter * 7573 + this.inductionCounter * 17 + this.rewritingCounter * 3;
        }
        
        @Override
        public int hashCode() {
            return hashCode;
        }

        @Override
        public boolean equals(final Object obj) {
            if (obj instanceof Options) {
                final Options option = (Options) obj;
                return this.leftChainCounter == option.leftChainCounter
                    && this.rightChainCounter == option.rightChainCounter
                    && this.inductionCounter == option.inductionCounter
                    && this.rewritingCounter == option.rewritingCounter;

            }
            return false;
        }

        @Override
        public String toString() {
            return " I"
                + this.inductionCounter
                + " L"
                + this.leftChainCounter
                + " R"
                + this.rightChainCounter
                + " RW"
                + this.rewritingCounter;
        }

    }

    protected abstract StrategyLevel[] initLeveledStrategy();

    protected abstract Set<FunctionSymbol> createNoHeadSymbols();

    protected abstract Map<FunctionSymbol, ImmutableSet<GeneralizedRule>> createRuleMap();

    protected abstract Set<FunctionSymbol> createConstructorSymbols();

    protected abstract Set<FunctionSymbol> createDefinedRSymbols();

    /**
     * @retrun true iff a given term is in normal form w.r.t the problem
     */
    @Override
    public abstract boolean isNormal(TRSTerm t);

    /**
     * rules of the problem, typically QDP or IDP problem
     */
    @Override
    public abstract Set<? extends GeneralizedRule> getRules();

    /**
     * Generates the initial implications (constraints) for a given problem and uses options provided
     * for cunstruction
     * @return the map of simplicated implications(constraints) for each chain of a pair
     * @throws AbortionException
     */
    public Map<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>> createConstraintSetProRule() {
        Map<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>> map = null;
        int lcc = this.options.leftChainCounter;
        int rcc = this.options.rightChainCounter;
        if (lcc == 0 && rcc == 0) {
            lcc = 1;
        }
        map = this.createConstraintSetProRule(lcc + rcc + 1, lcc);
        if (lcc == 0 && rcc == 0) {
            int realImp = 0;
            for (final Map.Entry<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>> entry : map.entrySet())
            {
                for (final Map.Entry<List<GeneralizedRule>, List<Implication>> entry2 : entry.getValue().entrySet()) {
                    for (final Implication imp : entry2.getValue()) {
                        if (!imp.getConditions().isEmpty()) {
                            realImp++;
                        }
                    }
                }
            }
            if (realImp == 0) {
                lcc = 0;
                rcc = 1;
                map = this.createConstraintSetProRule(lcc + rcc + 1, lcc);
            }
        }
        this.proof.fixedPosition = lcc;
        return map;
    }

    /**
     * Generates the initial implications (constraints) for a given problem
     * @param c chain length
     * @param position position of the dp in consideration
     * @return  a map from DPs to a map from chains to a list of
     *          initial implications (constraints) where the conditions are results of these chains
     *
     *  Formal:   form pair si->ti in chain s1->t1,...,sn->tn we get this
     *            initial implication (constraint):  t1=s2 and t2=s3 and ... and tn-1=sn ==> si->ti
     */
    public abstract Map<GeneralizedRule, Map<List<GeneralizedRule>, List<Implication>>> createConstraintSetProRule(
        int c,
        int position);

}
