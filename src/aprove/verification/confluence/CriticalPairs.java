package aprove.verification.confluence;

import java.util.*;
import java.util.stream.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.verification.confluence.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

public class CriticalPairs {

    public CriticalPairs(ConfTRSProblem confTrsProblem) {
        this(confTrsProblem.getRules(), confTrsProblem.getRuleMap());
    }

    private volatile AbortableIterator<CriticalPairInfo> critPairIterator;

    private Map<FunctionSymbol, ? extends Set<? extends GeneralizedRule>> ruleMap;

    private Boolean gotNonTrivialRootCritpair;
    private Boolean gotNonRootCritpairs;
    private Boolean gotCritpair;
    private Boolean gotNonTrivialCritpair;

    private Collection<Pair<CriticalPairInfo, Integer>> nonJoinableCritPairs;

    private Collection<CriticalPairInfo> possibleNCRCritPairs;

    private final List<CriticalPairInfo> allFoundCriticalPairs = new ArrayList<>();
    
    private final Map<CriticalPairInfo, Pair<ImmutableList<RewriteStep>, ImmutableList<RewriteStep>>> foundJoinable = new LinkedHashMap<>();

    private JoinableResult.WcrCounterExample counterExampleWCR;
    private JoinableResult.NonConfluent counterExampleCR;

    private CPK status = CPK.MAYBE;
    private int limit;

    private YNM allStronglyJoinable = YNM.MAYBE;
    
    private final Map<TRSTerm, ImmutableList<RewriteStep>> normalFormsReachable = new LinkedHashMap<>();

    public CriticalPairs(final Set<? extends GeneralizedRule> rls,
                         final Map<FunctionSymbol, ? extends Set<? extends GeneralizedRule>> ruleMap) {
        assert !Globals.useAssertions || (ruleMap != null && rls != null);

        this.critPairIterator = new CriticalPairGenerator(rls);
        this.ruleMap = ruleMap;
        this.nonJoinableCritPairs = ruleMap == null ? null : new LinkedList<>();
    }

    public List<CriticalPairInfo> getAllFoundCriticalPairs(final Abortion aborter) {
        if (this.allFoundCriticalPairs.isEmpty()) {
            this.getNextCritPair(aborter, false);
        }
        return Collections.unmodifiableList(this.allFoundCriticalPairs);
    }

    public JoinableResult.WcrCounterExample getCounterExampleWCR() {
        return this.counterExampleWCR;
    }
    
    public JoinableResult.NonConfluent getCounterExampleCR() {
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
    
    public Map<CriticalPairInfo, Pair<ImmutableList<RewriteStep>, ImmutableList<RewriteStep>>> getFoundJoinable() {
        return this.foundJoinable;
    }

    /**
     * Ensures that the strong joinability property has been determined by performing
     * a 1-step joinability check on all critical pairs. This is done only once
     * and the result is cached.
     * @param aborter
     * @return are the pairs Joinable in one Step
     */
    public synchronized void ensureStrongJoinabilityIsDetermined(final Abortion aborter) throws AbortionException {
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

            final JoinableResult result = CriticalPairs.critPairIsJoinable(
                                                                cpInfo,
                                                                0, // start
                                                                1, // limit
                                                                this.ruleMap,
                                                                this.normalFormsReachable,
                                                                SearchMode.EXIT_ON_FIRST_JOIN,
                                                                aborter);

            if (!(result instanceof JoinableResult.Joinable joinable)){
                this.allStronglyJoinable = YNM.NO;
                if (result instanceof JoinableResult.NonConfluent nonConfluent)
                    handleNonConfluence(nonConfluent);
                else if (result instanceof JoinableResult.WcrCounterExample wcrCounterExample)
                    handleNonWCR(wcrCounterExample);
                return;
            }

            this.handleJO(cpInfo, joinable, iter);
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
    private void getNextCritPair(final Abortion aborter, final boolean one) throws AbortionException {
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

                                if (si instanceof TRSFunctionApplication fsi && ti instanceof TRSFunctionApplication gti) {
                                    final FunctionSymbol f = fsi.getRootSymbol();
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
                                        // Neither f nor g is a valid root function symbol
                                        this.status = CPK.NOTWCR;
                                        this.allStronglyJoinable = YNM.NO;
                                        if (this.counterExampleWCR == null) {
                                            this.counterExampleWCR = new JoinableResult.WcrCounterExample.InvalidRootSymbol(currentCPInfo.sRule(), currentCPInfo.tRule(), f, g);
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

    private synchronized void checkJoin(final int limit, final Abortion aborter) throws AbortionException {
        if (limit > this.limit && this.status == CPK.MAYBE && this.nonJoinableCritPairs != null) {
            final Iterator<Pair<CriticalPairInfo, Integer>> critPairIter = this.nonJoinableCritPairs.iterator();
            while (critPairIter.hasNext()) {
                aborter.checkAbortion();
                final Pair<CriticalPairInfo, Integer> pair = critPairIter.next();
                final CriticalPairInfo cpInfo = pair.x;

                final JoinableResult result = CriticalPairs.critPairIsJoinable(
                    cpInfo,
                    pair.y,
                    limit,
                    this.ruleMap,
                    this.normalFormsReachable,
                    SearchMode.EXIT_ON_FIRST_JOIN,
                    aborter
                );

                if (result instanceof JoinableResult.Joinable joinable) {
                    handleJO(cpInfo, joinable, critPairIter);
                }
                else if (result instanceof JoinableResult.WcrCounterExample.NonJoinable nonJoinable) {
                    handleNonWCR(nonJoinable);
                    return;
                }
                else if (result instanceof JoinableResult.NonConfluent nonConfluent) {
                    handleNonConfluence(nonConfluent);
                }
                else {
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
    
    private synchronized void checkNonConfluence(final int limit, final Abortion aborter) throws AbortionException {
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

            final JoinableResult result = CriticalPairs.critPairIsJoinable(cpi, 0, limit, this.ruleMap, normalFormsReachable, SearchMode.EXHAUSTIVE_NON_CONFLUENCE, aborter);

            if (result instanceof JoinableResult.WcrCounterExample.NonJoinable nonJoinable) {
                this.handleNonWCR(nonJoinable);
                this.possibleNCRCritPairs = null;
                return;
            }
            else if (result instanceof JoinableResult.NonConfluent nonConfluent) {
                this.handleNonConfluence(nonConfluent);
                this.possibleNCRCritPairs = null;
                return;
            }
            else if (result instanceof JoinableResult.Joinable joinable) {
                this.handleJO(cpi, joinable, critPairIter);
            }
        }
        if (this.possibleNCRCritPairs.isEmpty()) {
            this.status = CPK.WCR_DONE;
        }
    }
    
    private void handleNonConfluence(JoinableResult.NonConfluent result) {
        this.status = CPK.NOTCR;
        this.counterExampleCR = result;
    }
    
    private void handleNonWCR(JoinableResult.WcrCounterExample result) {
        this.status = CPK.NOTWCR;
        if (this.counterExampleWCR == null)
            this.counterExampleWCR = result;
    }
    
    private <E> void handleJO(CriticalPairInfo cpi, JoinableResult.Joinable result, Iterator<E> iter) {
        if(!this.foundJoinable.containsKey(cpi))
            this.foundJoinable.put(cpi, new Pair<>(result.leftSequence(), result.rightSequence()));
        iter.remove();
    }

    public enum SearchMode {
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
    static <T extends GeneralizedRule> JoinableResult critPairIsJoinable(
            final CriticalPairInfo criticalPairInfo,
            final int start,
            final int limit,
            final Map<FunctionSymbol, ? extends Set<? extends T>> rules,
            Map<TRSTerm, ImmutableList<RewriteStep>> normalFormCache,
            SearchMode searchMode,
            final Abortion aborter) throws AbortionException {

        TrsTermJoinTree<T> joinTree = new TrsTermJoinTree<>(rules, criticalPairInfo, normalFormCache);
        return joinTree.areTermsJoinable(start, limit, searchMode, aborter);
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
                            final Pair<Position, TRSFunctionApplication> posAndSubLeft = this.currentOtherPositions.next();
                            final TRSFunctionApplication subLeft = posAndSubLeft.y;
                            final TRSSubstitution sigma = left.getMGU(subLeft);
                            if (sigma != null) {
                                final TRSTerm s = otherLeft.replaceAt(posAndSubLeft.x, right).applySubstitution(sigma);
                                final TRSTerm t = otherRight.applySubstitution(sigma);
                                // Additional Logic, new Crit Pair
                                final TRSTerm r = otherLeft.applySubstitution(sigma);
                                this.nextCritPair = new CriticalPairInfo(
                                        originalRootRule,
                                        originalOtherRule,
                                        s,
                                        t,
                                        false,
                                        r,
                                        posAndSubLeft.x);
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
                        this.nextCritPair = new CriticalPairInfo(originalRootRule, originalOtherRule, s, t, true, r, Position.EPSILON);
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
    }
}
