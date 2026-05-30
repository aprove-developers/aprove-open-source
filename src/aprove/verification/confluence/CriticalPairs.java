package aprove.verification.confluence;

import java.util.*;
import java.util.stream.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.confluence.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class CriticalPairs {

    public CriticalPairs(ConfTRSProblem conftrs) {
        this(conftrs.getRules(), conftrs.getRuleMap());
    }

    private volatile AbortableIterator<CriticalPairInfo> critPairIterator;

    private Map<FunctionSymbol, ? extends Set<? extends GeneralizedRule>> ruleMap;

    private Boolean gotNonTrivialRootCritpair;
    private Boolean gotNonRootCritpairs;
    private Boolean gotCritpair;
    private Boolean gotNonTrivialCritpair;

    private Collection<Pair<CriticalPairInfo, Integer>> nonJoinableCritPairs;
    
    private Collection<CriticalPairInfo> possibleNCRCritPairs;

    private final List<CriticalPairInfo> allFoundCriticalPairs;
    
    private Map<CriticalPairInfo, TRSTerm> foundJoinable;
    
    private CriticalPairInfo counterExampleWCR;
    private Triple<CriticalPairInfo, TRSTerm, TRSTerm> counterExampleCR;

    private CPK status;
    private int limit;

    private YNM allStronglyJoinable;
    
    private Map<TRSTerm, TRSTerm> normalFormsReachable;

    public CriticalPairs(final Set<? extends GeneralizedRule> rls,
                         final Map<FunctionSymbol, ? extends Set<? extends GeneralizedRule>> ruleMap) {
        if (Globals.useAssertions) {
            assert (ruleMap != null && rls != null);
        }
        this.critPairIterator = new CriticalPairGenerator(rls);

        this.ruleMap = ruleMap;
        this.gotNonRootCritpairs = null;
        this.gotCritpair = null;
        this.gotNonTrivialRootCritpair = null;
        this.gotNonTrivialCritpair = null;
        this.nonJoinableCritPairs = ruleMap == null ? null : new LinkedList<>();
        this.foundJoinable = new LinkedHashMap<CriticalPairInfo, TRSTerm>();
        this.status = CPK.MAYBE;
        this.limit = 0;

        this.allFoundCriticalPairs = new ArrayList<>();
        this.counterExampleWCR = null;

        this.allStronglyJoinable = YNM.MAYBE;
        
        this.normalFormsReachable = new LinkedHashMap<TRSTerm, TRSTerm>();
        
        this.possibleNCRCritPairs = null;
    }

    public List<CriticalPairInfo> getAllFoundCriticalPairs(final Abortion aborter) {
        if (this.allFoundCriticalPairs == null) {
            this.getNextCritPair(aborter, false);
        }
        return Collections.unmodifiableList(this.allFoundCriticalPairs);
    }

    public CriticalPairInfo getCounterExampleWCR() {
        return this.counterExampleWCR;
    }
    
    public Triple<CriticalPairInfo, TRSTerm, TRSTerm> getCounterExampleCR(){
        return this.counterExampleCR;
    }

    /**
     * checks whether we have a non-overlapping set of rules
     * @param aborter
     * @return
     * @throws AbortionException
     */
    public synchronized boolean isNonOverlapping(final Abortion aborter) throws AbortionException {
        if (this.gotCritpair == null) {
            this.getNextCritPair(aborter, true);
        }
        return !this.gotCritpair;
    }

    /**
     * checks whether we have a an overlay TRS, ie. where the only
     * critical pairs are on root level
     * @param aborter
     * @return
     * @throws AbortionException
     */
    public synchronized boolean isOverlay(final Abortion aborter) throws AbortionException {
        if (this.gotNonRootCritpairs == null) {
            this.getNextCritPair(aborter, true);
        }
        return !this.gotNonRootCritpairs;
    }

    /**
     * checks whether we have innermost confluence, where as criterion
     * we check whether all root-overlaps are trivial
     * @param aborter
     * @return
     * @throws AbortionException
     */
    public synchronized boolean isInnermostConfluent(final Abortion aborter) throws AbortionException {
        while (this.gotNonTrivialRootCritpair == null) {
            this.getNextCritPair(aborter, true);
        }
        return !this.gotNonTrivialRootCritpair;
    }
    
    public synchronized Collection<CriticalPairInfo> getPossibleNCRCritPairs(Abortion aborter){
        if (this.possibleNCRCritPairs == null && !this.status.isDefinitiveAnswer()) {
            this.possibleNCRCritPairs = this.getAllFoundCriticalPairs(aborter).stream()
                    .filter(cpi -> !cpi.s().equals(cpi.t()))
                    .collect(Collectors.toCollection(LinkedList<CriticalPairInfo>::new));
        }
        return this.possibleNCRCritPairs;
    }
    
    public Map<CriticalPairInfo, TRSTerm> getFoundJoinable() {
        return this.foundJoinable;
    }

    /**
     * Ensures that the strong joinability property has been determined by performing
     * a 1-step joinability check on all critical pairs. This is done only once
     * and the result is cached.
     * @param aborter
     * @return are the pairs Joinable in one Step
     */
    private synchronized void ensureStrongJoinabilityIsDetermined(final Abortion aborter) throws AbortionException {
        if (this.allStronglyJoinable != YNM.MAYBE) {
            // Already determined, do nothing.
            return;
        }
        
        if(this.onlyTrivialCriticalPairs(aborter)) {
            this.allStronglyJoinable = YNM.YES;
            this.status = CPK.WCR_DONE;
            return;
        }

        // This call ensures this.allFoundCriticalPairs is populated.
        this.getNextCritPair(aborter, false);
        
        Iterator<Pair<CriticalPairInfo, Integer>> iter = this.nonJoinableCritPairs.iterator();
        while(iter.hasNext()) {
            aborter.checkAbortion();
            Pair<CriticalPairInfo, Integer> pair = iter.next();
            CriticalPairInfo cpInfo = pair.x;

            final JoinRes result = CriticalPairs.critPairIsJoinable(
                                                                cpInfo.s(),
                                                                cpInfo.t(),
                                                                0, // start
                                                                1, // limit
                                                                this.ruleMap,
                                                                this.normalFormsReachable,
                                                                SearchMode.EXIT_ON_FIRST_JOIN,
                                                                aborter);
            
            final CPT truth = result.truth();

            if (truth != CPT.Joinable) {
                this.allStronglyJoinable = YNM.NO;
                if (truth == CPT.NonConfluent) {
                  this.handleNonConfluence(result, cpInfo); 
                }
                if (truth == CPT.NonJoinable) {
                    this.handleNonWCR(cpInfo);
                }
                return;
            }
            this.handleJO(cpInfo, result, iter);
            
            
        }

        this.status = CPK.WCR;
        this.allStronglyJoinable = YNM.YES;
    }

    public synchronized YNM areAllCriticalPairsStronglyJoinable(final Abortion aborter) throws AbortionException {
        this.ensureStrongJoinabilityIsDetermined(aborter);
        return this.allStronglyJoinable;
    }
    
    public synchronized CPK checkStatusWeak(final int limit, final Abortion aborter) throws AbortionException {
        
        this.ensureStrongJoinabilityIsDetermined(aborter);
        
        if(this.status.isAnyAnswer()) {
            return this.status;
        }
        
        if (this.critPairIterator != null) {
            this.getNextCritPair(aborter, false);
        }
        if (this.limit >= limit || this.status.isAnyAnswer()) {
            return this.status;
        }
        this.checkJoin(limit, aborter);
        return this.status;
    }
    
    public synchronized CPK checkStatusWeak(final Abortion aborter) throws AbortionException {
        int limit = 8;
        CPK status = null;
        while(limit < Integer.MAX_VALUE / 2 - 2) {
            status = this.checkStatusWeak(limit, aborter);
            if(this.status.isAnyAnswer())
                return status;
            limit *= 2;
        }
        return status;
    }
    
    public synchronized CPK checkStatusDefinitive(final Abortion aborter) throws AbortionException {
        int limit = 8;
        CPK status = null;
        while(limit < Integer.MAX_VALUE / 2 - 2) {
            status = this.checkStatusDefinitive(limit, aborter);
            if(this.status.isDefinitiveAnswer())
                return status;
            
            limit *= 2;
        }
        return status;
    }
    
    
    public synchronized CPK checkStatusDefinitive(final int limit, final Abortion aborter) throws AbortionException {
        this.ensureStrongJoinabilityIsDetermined(aborter);
        if(this.status.isDefinitiveAnswer()) {
            return this.status;
        }
        if(this.critPairIterator != null) {
            this.getNextCritPair(aborter, false);
        }
        if (this.limit >= limit || this.status.isDefinitiveAnswer()) {
            return this.status;
        }
        this.checkNonConfluence(limit, aborter);
        return this.status;
    }

    public synchronized boolean onlyTrivialCriticalPairs(final Abortion aborter) throws AbortionException {
        while (this.gotNonTrivialCritpair == null) {
            this.getNextCritPair(aborter, true);
        }
        return !this.gotNonTrivialCritpair;
    }

    /**
     * computes one next critical pair or all critical pairs
     * @param aborter
     * @param one: only generate one critical pair (true), or generate all critical pairs (false)
     * @throws AbortionException
     */
    private final void getNextCritPair(final Abortion aborter, final boolean one) throws AbortionException {
        if (this.critPairIterator != null) {
            synchronized (this) {
                if (this.critPairIterator != null) {
                    final ArrayStack<Pair<CriticalPairInfo, Integer>> todoList = new ArrayStack<>();
                    boolean notDone = true;
                    while (notDone) {
                        if (one) {
                            notDone = false;
                        }
                        if (this.critPairIterator.hasNext(aborter)) {
                            final CriticalPairInfo currentCPInfo = this.critPairIterator.next(aborter);
                            this.allFoundCriticalPairs.add(currentCPInfo);

                            final TRSTerm s = currentCPInfo.s();
                            final TRSTerm t = currentCPInfo.t();

                            if (this.gotCritpair == null) {
                                // found first critical pair
                                this.gotCritpair = true;
                                if (currentCPInfo.isRootOverlap()) {
                                    if (!s.equals(t)) {
                                        this.gotNonTrivialRootCritpair = true;
                                    }
                                    this.gotNonRootCritpairs = false;
                                } else {
                                    this.gotNonRootCritpairs = true;
                                }
                            } else {
                                if (this.gotNonTrivialRootCritpair == null && currentCPInfo.isRootOverlap()
                                    && !s.equals(t)) {
                                    this.gotNonTrivialRootCritpair = true;
                                }
                            }

                            if (this.gotNonTrivialCritpair == null && !s.equals(t)) {
                                this.gotNonTrivialCritpair = true;
                            }

                            final ArrayStack<Pair<TRSTerm, TRSTerm>> decompositionStack = new ArrayStack<>();
                            decompositionStack.push(new Pair<>(s, t));
                            boolean needsRewriteCheck = false;

                            while (!decompositionStack.isEmpty()) {
                                final Pair<TRSTerm, TRSTerm> todo = decompositionStack.pop();
                                final TRSTerm si = todo.x;
                                final TRSTerm ti = todo.y;
                                if (si.equals(ti))
                                    continue;

                                if (si instanceof TRSFunctionApplication && ti instanceof TRSFunctionApplication) {
                                    final TRSFunctionApplication fsi = (TRSFunctionApplication) si;
                                    final FunctionSymbol f = fsi.getRootSymbol();
                                    final TRSFunctionApplication gti = (TRSFunctionApplication) ti;
                                    final FunctionSymbol g = gti.getRootSymbol();

                                    if (this.ruleMap.containsKey(f) || this.ruleMap.containsKey(g)) {
                                        needsRewriteCheck = true;
                                        break;
                                    }
                                    if (f.equals(g)) {
                                        final Iterator<? extends TRSTerm> siArgs = fsi.getArguments().iterator();
                                        for (final TRSTerm tiArg : gti.getArguments()) {
                                            decompositionStack.push(new Pair<>(siArgs.next(), tiArg));
                                        }
                                    } else {
                                        this.status = CPK.NOTWCR;
                                        this.allStronglyJoinable = YNM.NO;
                                        if (this.counterExampleWCR == null) {
                                            this.counterExampleWCR = currentCPInfo;
                                        }
                                        this.ruleMap = null;
                                        this.nonJoinableCritPairs = null;
                                        this.critPairIterator = null;
                                        return;
                                    }
                                } else {
                                    needsRewriteCheck = true;
                                    break;
                                }
                            }
                            if (needsRewriteCheck) {
                                this.nonJoinableCritPairs.add(new Pair<>(currentCPInfo, 0));
                            }
                        } else {
                            notDone = false;
                            this.critPairIterator = null;
                            if (this.gotNonTrivialCritpair == null) {
                                this.gotNonTrivialCritpair = false;
                            }
                            if (this.gotCritpair == null) {
                                this.gotCritpair = false;
                                this.gotNonTrivialRootCritpair = false;
                                this.gotNonRootCritpairs = false;
                                this.ruleMap = null;
                                this.nonJoinableCritPairs = null;
                                this.status = CPK.WCR;
                                this.allStronglyJoinable = YNM.YES;
                            } else {
                                if (this.gotNonTrivialRootCritpair == null) {
                                    this.gotNonTrivialRootCritpair = false;
                                }
                                if (this.nonJoinableCritPairs.isEmpty()) {
                                    this.status = CPK.WCR;
                                    this.allStronglyJoinable = YNM.YES;
                                    this.nonJoinableCritPairs = null;
                                } else {
                                    this.status = CPK.MAYBE;
                                }
                            }
                        }
                    }
                }
            }
        }
    }
    
    
    
    private final synchronized void checkJoin(final int limit, final Abortion aborter) throws AbortionException {
        if (limit > this.limit && this.status == CPK.MAYBE && this.nonJoinableCritPairs != null) {
            final Iterator<Pair<CriticalPairInfo, Integer>> critPairIter = this.nonJoinableCritPairs.iterator();
            while (critPairIter.hasNext()) {
                aborter.checkAbortion();
                final Pair<CriticalPairInfo, Integer> pair = critPairIter.next();
                final CriticalPairInfo cpInfo = pair.x;

                final JoinRes result = CriticalPairs.critPairIsJoinable(cpInfo.s(),
                                                                    cpInfo.t(),
                                                                    pair.y,
                                                                    limit,
                                                                    this.ruleMap,
                                                                    this.normalFormsReachable,
                                                                    SearchMode.EXIT_ON_FIRST_JOIN,
                                                                    aborter);
                final CPT truth = result.truth();
                if (truth == CPT.Joinable) {
                    this.handleJO(cpInfo, result, critPairIter);
                } else if (truth == CPT.NonJoinable) {
                    this.status = CPK.NOTWCR;
                    if (this.counterExampleWCR == null) {
                        this.counterExampleWCR = cpInfo;
                    }
                    //this.ruleMap = null;
                    //this.nonJoinableCritPairs = null;
                    return;
                } else if (truth == CPT.NonConfluent) {
                    this.handleNonConfluence(result, cpInfo);
                    return;
                } else {
                    this.limit = limit;
                    // one might do a return here,
                    // but we also search the other pairs for possible no's
                }
            }
            if (this.nonJoinableCritPairs.isEmpty()) {
                this.status = CPK.WCR;
                this.nonJoinableCritPairs = null;
                // this.ruleMap = null;
            }
        }
    }
    
    private static boolean CPKIsNCR(CPK cpk) {
        return cpk == CPK.NOTCR || cpk == CPK.NOTCR;
    }
    
    private static boolean cpIsTrivial(CriticalPairInfo cpi)
    {
        return cpi.s().equals(cpi.t());
    }
    
    private final synchronized void checkNonConfluence(final int limit, final Abortion aborter) throws AbortionException {
        if(limit <= this.limit || CPKIsNCR(this.status)) {
            return ;
        }
        this.getPossibleNCRCritPairs(aborter);
        final Iterator<CriticalPairInfo> critPairIter = this.possibleNCRCritPairs.iterator();
        while (critPairIter.hasNext()) {
            aborter.checkAbortion();
            final CriticalPairInfo cpi = critPairIter.next();
            if (cpIsTrivial(cpi)) {
                critPairIter.remove();
                continue;
            }
            final JoinRes result = CriticalPairs.critPairIsJoinable(cpi.s(), cpi.t(), 0, limit, this.ruleMap, normalFormsReachable, SearchMode.EXHAUSTIVE_NON_CONFLUENCE, aborter);
            
            final CPT truth = result.truth();
            if (truth == CPT.NonJoinable) {
                this.handleNonWCR(cpi);
                this.possibleNCRCritPairs = null;
                return;
            }
            else if (truth == CPT.NonConfluent) {
                this.handleNonConfluence(result, cpi);
                this.possibleNCRCritPairs = null;
                return;
            }
            else if (truth == CPT.Joinable) {
                this.handleJO(cpi, result, critPairIter);
            }
        }
        if(this.possibleNCRCritPairs.isEmpty()) {
            this.status = CPK.WCR_DONE;
        }
    }
    
    private void handleNonConfluence(JoinRes result, CriticalPairInfo cpInfo) {
        this.status = CPK.NOTCR;
        TRSTerm s = result.s();
        TRSTerm t = result.t();
        this.counterExampleCR = new Triple<CriticalPairInfo, TRSTerm, TRSTerm>(cpInfo, s, t);
    }
    
    private void handleNonWCR(CriticalPairInfo cpInfo) {
        this.status = CPK.NOTWCR;
        if (this.counterExampleWCR == null)
            this.counterExampleWCR = cpInfo;
    }
    
    private <E> void handleJO(CriticalPairInfo cpi, JoinRes result, Iterator<E> iter) {
        if(!this.foundJoinable.containsKey(cpi))
            this.foundJoinable.put(cpi, result.s());
        iter.remove();
    }
    
    
    

    private static final int countSteps = 1 << 6;
    
    
    private record JoinRes(CPT truth, TRSTerm s, TRSTerm t) {
        static JoinRes create(CPT truth) {
            return new JoinRes(truth, null, null);
        }
        static JoinRes create(CPT truth, TRSTerm n) {
            return new JoinRes(truth, n, null);
        }
        static JoinRes create(CPT truth, TRSTerm s, TRSTerm t) {
            return new JoinRes(truth, s, t);
        }
    };
    
    private enum CPT { Joinable, NonJoinable, NonConfluent, Maybe;
    }
    
    
    private enum SearchMode {
        EXIT_ON_FIRST_JOIN,
        EXHAUSTIVE_NON_CONFLUENCE
        
    }

    /**
     * Check if a given critical pair is joinable in <code>limit</code> rewriting steps, where it has been checked that
     * it is not joinable in start steps.
     * @param start a natural number
     * @param limit a natural number
     * @throws AbortionException
     */
    static final <T extends GeneralizedRule>
           JoinRes
           critPairIsJoinable(final TRSTerm cpLeft,
                              final TRSTerm cpRight,
                              final int start,
                              final int limit,
                              final Map<FunctionSymbol, ? extends Set<? extends T>> Rls,
                              Map<TRSTerm, TRSTerm> normalFormCache,
                              SearchMode searchMode,
                              final Abortion aborter) throws AbortionException {
        int count = 0;
        if (start >= limit) {
            return JoinRes.create(CPT.Maybe);
        }
        boolean isJoinable = false;
        TRSTerm leftNF = null;
        TRSTerm rightNF = null;
        if (normalFormCache != null) {
            leftNF = normalFormCache.get(cpLeft);
            rightNF = normalFormCache.get(cpRight);
            if (leftNF != null && rightNF != null) {
                if (!leftNF.equals(rightNF)) {
                    return JoinRes.create(CPT.NonConfluent, leftNF, rightNF);
                }
                // else if (searchMode == SearchMode.EXIT_ON_FIRST_JOIN) return JoinRes.create(CPT.Joinable);
            }
        }
        TRSTerm normalForm = rightNF == null ? leftNF : rightNF;
        TRSTerm joinTerm = null;
        
        Set<TRSTerm> leftNewTerms = new LinkedHashSet<>(), leftVeryNewTerms = new LinkedHashSet<>(),
                rightVeryNewTerms = new LinkedHashSet<>(), rightNewTerms = new LinkedHashSet<>();
        final Set<TRSTerm> leftAllTerms = new LinkedHashSet<>(), rightAllTerms = new LinkedHashSet<>();
        leftNewTerms.add(cpLeft);
        leftAllTerms.add(cpLeft);
        rightNewTerms.add(cpRight);
        rightAllTerms.add(cpRight);
        
        Set<TRSTerm> exchange;
        final FreshNameGenerator freshNames = new FreshNameGenerator(FreshNameGenerator.VARIABLES);
        freshNames.lockNames(CollectionUtils.getNames(cpLeft.getVariables()));
        freshNames.lockNames(CollectionUtils.getNames(cpRight.getVariables()));

        for (int i = 0; i < limit; i++) {
            // rewrite only those terms which have not been rewritten yet
            for (final TRSTerm leftNewTerm : leftNewTerms) {
                boolean rewritten = false;
                for (final TRSTerm leftRewriteTerm : leftNewTerm.rewriteGeneralized(Rls, freshNames)) {
                    rewritten = true;
                    if ((++count & CriticalPairs.countSteps) == 0)
                        aborter.checkAbortion();
                    if (leftAllTerms.add(leftRewriteTerm)) {
                        if (i >= start && rightAllTerms.contains(leftRewriteTerm)) {
                            if(searchMode == SearchMode.EXIT_ON_FIRST_JOIN) return JoinRes.create(CPT.Joinable, leftRewriteTerm);
                            joinTerm = leftRewriteTerm;
                        }
                        leftVeryNewTerms.add(leftRewriteTerm);
                    }
                }
                if (!rewritten) {
                    if (normalFormCache.get(cpLeft) == null) normalFormCache.put(cpLeft, leftNewTerm);
                    if (normalForm == null) normalForm = leftNewTerm;
                    else if (!normalForm.equals(leftNewTerm))
                        return JoinRes.create(CPT.NonConfluent, normalForm, leftNewTerm);
                }
            }
            // for next iteration
            exchange = leftNewTerms;
            leftNewTerms = leftVeryNewTerms;
            leftVeryNewTerms = exchange;
            leftVeryNewTerms.clear();

            // rewrite only those terms which have not been rewrited yet
            for (final TRSTerm rightNewTerm : rightNewTerms) {
                boolean rewritten = false;
                
                for (final TRSTerm rightRewriteTerm : rightNewTerm.rewriteGeneralized(Rls, freshNames)) {
                    rewritten = true;
                    if ((++count & CriticalPairs.countSteps) == 0)
                        aborter.checkAbortion();
                    if (rightAllTerms.add(rightRewriteTerm)) {
                        if (i >= start && leftAllTerms.contains(rightRewriteTerm)) {
                            if (searchMode == SearchMode.EXIT_ON_FIRST_JOIN) return JoinRes.create(CPT.Joinable, rightRewriteTerm);
                            joinTerm = rightRewriteTerm;
                        }
                        rightVeryNewTerms.add(rightRewriteTerm);
                    }
                }
                
                if (!rewritten) {
                    if (normalFormCache.get(cpRight) == null) normalFormCache.put(cpRight, rightNewTerm);
                    if (normalForm == null) normalForm = rightNewTerm;
                    else if (!normalForm.equals(rightNewTerm)) return JoinRes.create(CPT.NonConfluent, normalForm, rightNewTerm);
                }
            }
            //for next iteration
            exchange = rightNewTerms;
            rightNewTerms = rightVeryNewTerms;
            rightVeryNewTerms = exchange;
            rightVeryNewTerms.clear();
            if (leftNewTerms.isEmpty() && rightNewTerms.isEmpty()) {
                if (joinTerm != null) return JoinRes.create(CPT.Joinable, joinTerm);
                return JoinRes.create(CPT.NonJoinable);
            }
        }
        
        return JoinRes.create(CPT.Maybe);
    }
    
    // This private inner class is copied from GeneralizedRule.java and modified
    // to produce CriticalPairInfo objects, which include the source rules.
    private static class CriticalPairGenerator implements AbortableIterator<CriticalPairInfo> {

        private static final int MASK = 0x20;
        private final GeneralizedRule[] renumberedRules;
        private final GeneralizedRule[] originalRules; 
        private int posRoot, posOther;
        private final int n, n_minus_1;
        private boolean nextValid;
        private CriticalPairInfo nextCritPair;
        private Iterator<Pair<Position, TRSFunctionApplication>> currentOtherPositions;
        private int count = 0;

        private CriticalPairGenerator(Set<? extends GeneralizedRule> rules) {
            this.n = rules.size();
            this.n_minus_1 = this.n - 1;
            this.renumberedRules = new GeneralizedRule[this.n];
            this.originalRules = new GeneralizedRule[this.n];
            int i = 0;
            for (GeneralizedRule rule : rules) {
                this.originalRules[i] = rule;
                this.renumberedRules[i] = rule.getWithRenumberedVariables(TRSTerm.SECOND_STANDARD_PREFIX);
                i++;
            }
            if (this.n == 0) {
                this.nextValid = true;
            } else {
                this.nextValid = false;
                this.currentOtherPositions = this.renumberedRules[0].getLeft()
                                                                    .getNonRootNonVariablePositionsWithSubTerms()
                                                                    .iterator();
            }
            this.posRoot = 0;
            this.posOther = 0;
            this.nextCritPair = null;
        }

        private void computeNext(Abortion aborter) throws AbortionException {
            if (this.currentOtherPositions != null) {
                while (this.posRoot != this.n) {
                    final GeneralizedRule rootRule = this.renumberedRules[this.posRoot];
                    final GeneralizedRule originalRootRule = this.originalRules[this.posRoot];
                    final TRSTerm left = rootRule.getLhsInStandardRepresentation();
                    final TRSTerm right = rootRule.getRhsInStandardRepresentation();
                    while (this.posOther != this.n) {
                        final GeneralizedRule otherRule = this.renumberedRules[this.posOther];
                        final GeneralizedRule originalOtherRule = this.originalRules[this.posOther]; 
                        final TRSTerm otherLeft = otherRule.getLeft();
                        final TRSTerm otherRight = otherRule.getRight();
                        if (this.currentOtherPositions == null) {
                            this.currentOtherPositions = otherLeft.getNonRootNonVariablePositionsWithSubTerms()
                                                                  .iterator();
                        }
                        while (this.currentOtherPositions.hasNext()) {
                            if ((++this.count & CriticalPairGenerator.MASK) == 0)
                                aborter.checkAbortion();
                            final Pair<Position, TRSFunctionApplication> posAndSubLeft =
                                                                                       this.currentOtherPositions.next();
                            final TRSFunctionApplication subLeft = posAndSubLeft.y;
                            final TRSSubstitution sigma = left.getMGU(subLeft);
                            if (sigma != null) {
                                final TRSTerm s = otherRight.applySubstitution(sigma);
                                final TRSTerm t = otherLeft.replaceAt(posAndSubLeft.x, right).applySubstitution(sigma);
                                // Additional Logic, new Crit Pair
                                final TRSTerm r = otherLeft.applySubstitution(sigma);
                                this.nextCritPair = new CriticalPairInfo(asSet(originalRootRule, originalOtherRule),
                                                                         s,
                                                                         t,
                                                                         false,
                                                                         r);
                                this.nextValid = true;
                                return;
                            }
                        }
                        this.posOther++;
                        this.currentOtherPositions = null;
                    }
                    this.posRoot++;
                    this.posOther = 0;
                }
                this.posRoot = 0;
                this.posOther = 1;
            }
            while (this.posRoot != this.n_minus_1) {
                final GeneralizedRule rootRule = this.renumberedRules[this.posRoot];
                final GeneralizedRule originalRootRule = this.originalRules[this.posRoot]; // NEW
                final TRSTerm left = rootRule.getLhsInStandardRepresentation();
                final TRSTerm right = rootRule.getRhsInStandardRepresentation();
                while (this.posOther != this.n) {
                    final GeneralizedRule otherRule = this.renumberedRules[this.posOther];
                    final GeneralizedRule originalOtherRule = this.originalRules[this.posOther]; // NEW
                    final TRSTerm otherLeft = otherRule.getLeft();
                    this.posOther++;
                    final TRSSubstitution sigma = left.getMGU(otherLeft);
                    if (sigma != null) {
                        final TRSTerm s = right.applySubstitution(sigma);
                        final TRSTerm t = otherRule.getRight().applySubstitution(sigma);
                        final TRSTerm r = left.applySubstitution(sigma);
                        this.nextCritPair = new CriticalPairInfo(asSet(originalRootRule, originalOtherRule), s, t, true, r);
                        this.nextValid = true;
                        return;
                    }
                }
                this.posRoot++;
                this.posOther = this.posRoot + 1;
            }
            this.nextCritPair = null;
            this.nextValid = true;
        }

        @Override
        public boolean hasNext(Abortion aborter) throws AbortionException {
            if (!this.nextValid) {
                this.computeNext(aborter);
            }
            return this.nextCritPair != null;
        }

        @Override
        public CriticalPairInfo next(Abortion aborter) throws AbortionException {
            if (this.hasNext(aborter)) {
                this.nextValid = false;
                return this.nextCritPair;
            } else {
                throw new NoSuchElementException();
            }
        }
        
        private static ImmutableLinkedHashSet<GeneralizedRule> asSet(GeneralizedRule e1, GeneralizedRule e2){
            Set<GeneralizedRule> i = e1.equals(e2) ? Set.of(e1) : Set.of(e1, e2);
            final LinkedHashSet<GeneralizedRule> es = i.stream()
                    .collect(Collectors.toCollection(LinkedHashSet<GeneralizedRule>::new));
            return ImmutableCreator.create(es);
        }
    }
}
