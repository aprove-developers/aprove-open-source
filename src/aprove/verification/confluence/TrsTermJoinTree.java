package aprove.verification.confluence;

import aprove.strategies.Abortions.Abortion;
import aprove.verification.confluence.Utility.CriticalPairInfo;
import aprove.verification.dpframework.BasicStructures.CollectionUtils;
import aprove.verification.dpframework.BasicStructures.GeneralizedRule;
import aprove.verification.dpframework.BasicStructures.Position;
import aprove.verification.dpframework.BasicStructures.TRSTerm;
import aprove.verification.oldframework.BasicStructures.FunctionSymbol;
import aprove.verification.oldframework.Utility.FreshNameGenerator;
import aprove.verification.oldframework.Utility.GenericStructures.BiTreeNode;
import immutables.ImmutableCreator;
import immutables.ImmutableList;

import java.util.*;

public class TrsTermJoinTree<T extends GeneralizedRule> {
    private final Map<FunctionSymbol, ? extends Set<? extends T>> rules;
    private final CriticalPairInfo cpInfo;
    private final TRSTerm s;
    private final TRSTerm t;
    private final Map<TRSTerm, ImmutableList<RewriteStep>> normalFormCache;
    private final HashMap<TRSTerm, BiTreeNode<RewriteStep>> sLazySubstitutions = new HashMap<>();
    private final HashMap<TRSTerm, BiTreeNode<RewriteStep>> tLazySubstitutions = new HashMap<>();
    private final FreshNameGenerator freshNames = new FreshNameGenerator(FreshNameGenerator.VARIABLES);
    private Set<BiTreeNode<RewriteStep>> sLastLayer = new LinkedHashSet<>();
    private Set<BiTreeNode<RewriteStep>> tLastLayer = new LinkedHashSet<>();
    private ImmutableList<RewriteStep> foundNormalForm;

    public TrsTermJoinTree(Map<FunctionSymbol, ? extends Set<? extends T>> rules, CriticalPairInfo cpInfo, Map<TRSTerm, ImmutableList<RewriteStep>> normalFormCache) {
        this(rules, cpInfo.s(), cpInfo.t(), new BiTreeNode<>(new RewriteStep(cpInfo.divergence(), Position.EPSILON, cpInfo.sRule(), cpInfo.s())), new BiTreeNode<>(new RewriteStep(cpInfo.divergence(), Position.EPSILON, cpInfo.tRule(), cpInfo.t())), normalFormCache, cpInfo);
    }

    public TrsTermJoinTree(Map<FunctionSymbol, ? extends Set<? extends T>> rules, TRSTerm s, TRSTerm t) {
        this(rules, s, t, new BiTreeNode<>(new RewriteStep(null, null, null, s)), new BiTreeNode<>(new RewriteStep(null, null, null, t)), null, null);
    }

    private TrsTermJoinTree(Map<FunctionSymbol, ? extends Set<? extends T>> rules, TRSTerm s, TRSTerm t, BiTreeNode<RewriteStep> sTree, BiTreeNode<RewriteStep> tTree, Map<TRSTerm, ImmutableList<RewriteStep>> normalFormCache, CriticalPairInfo cpInfo) {
        this.rules = rules;
        this.cpInfo = cpInfo;
        this.s = s;
        this.t = t;
        this.normalFormCache = normalFormCache;
        this.sLastLayer.add(sTree);
        this.tLastLayer.add(tTree);
        freshNames.lockNames(CollectionUtils.getNames(s.getVariables()));
        freshNames.lockNames(CollectionUtils.getNames(t.getVariables()));
    }

    JoinableResult areTermsJoinable(int start, int limit, CriticalPairs.SearchMode searchMode, Abortion aborter) {
        if (start >= limit)
            return new JoinableResult.Maybe();

        if (normalFormCache != null) {
            ImmutableList<RewriteStep> leftNF = normalFormCache.get(s);
            ImmutableList<RewriteStep> rightNF = normalFormCache.get(t);
            if (leftNF != null && rightNF != null && leftNF.size() > 1 && rightNF.size() > 1 && !leftNF.getLast().substitutedTerm().equals(rightNF.getLast().substitutedTerm()))
                return new JoinableResult.WcrCounterExample.NonConfluent(leftNF, rightNF);
            if (leftNF != null && leftNF.size() > 1)
                foundNormalForm = leftNF;
            else if (rightNF != null && rightNF.size() > 1)
                foundNormalForm = rightNF;
        }

        // TODO: actually implement start argument
        for (int i = 0; i < limit; i++) {
            JoinableResult sResult = buildTreeLayer(s, sLastLayer, sLazySubstitutions, tLazySubstitutions, searchMode, aborter);
            if (!(sResult instanceof NewLayer(Set<BiTreeNode<RewriteStep>> sNewLayer)))
                return sResult;
            sLastLayer = sNewLayer;

            var tResult = buildTreeLayer(t, tLastLayer, tLazySubstitutions, sLazySubstitutions, searchMode, aborter);
            if (!(tResult instanceof NewLayer(Set<BiTreeNode<RewriteStep>> tNewLayer)))
                return tResult;
            tLastLayer = tNewLayer;

            // TODO: Implement searchMode. At this point, we would need to check if we found a join term and return a JoinableResult.Joinable
            if (sNewLayer.isEmpty() && tNewLayer.isEmpty())
                return new JoinableResult.WcrCounterExample.NonJoinable(cpInfo);
        }

        return new JoinableResult.Maybe();
    }

    record NewLayer(Set<BiTreeNode<RewriteStep>> newLayer) implements JoinableResult {}

    private JoinableResult buildTreeLayer(
            TRSTerm root,
            Set<BiTreeNode<RewriteStep>> lastLayer,
            HashMap<TRSTerm, BiTreeNode<RewriteStep>> lazyFoundOwnSubstitutions,
            HashMap<TRSTerm, BiTreeNode<RewriteStep>> lazyFoundOtherSubstitutions,
            CriticalPairs.SearchMode searchMode,
            Abortion aborter) {

        Set<BiTreeNode<RewriteStep>> newLayer = new LinkedHashSet<>();
        for (BiTreeNode<RewriteStep> lastLayerNode : lastLayer) {
            aborter.checkAbortion();
            var possibleRewrites = lastLayerNode.getValue().substitutedTerm().computePossibleRewrites(rules, freshNames);

            // No further rewrites possible, we found a normal formal
            if (possibleRewrites.isEmpty()){
                ImmutableList<RewriteStep> sequence = buildRewriteSequence(lastLayerNode);
                if (normalFormCache != null)
                    normalFormCache.putIfAbsent(root, sequence);

                // Check if we previously found a normal form.
                // If so, the TRS cannot be confluent
                if (foundNormalForm == null)
                    foundNormalForm = sequence;
                else if (!foundNormalForm.getLast().substitutedTerm().equals(lastLayerNode.getValue().substitutedTerm()))
                    return new JoinableResult.WcrCounterExample.NonConfluent(foundNormalForm, sequence);
            }

            // Otherwise, brute force all possible rewrite steps and add them to the tree
            for (final RewriteStep rewriteStep : possibleRewrites) {
                BiTreeNode<RewriteStep> stepNode = new BiTreeNode<>(rewriteStep);
                lastLayerNode.addChild(stepNode);
                newLayer.add(stepNode);
                if (!lazyFoundOwnSubstitutions.containsKey(rewriteStep.substitutedTerm())) {
                    if (lazyFoundOtherSubstitutions.containsKey(rewriteStep.substitutedTerm()))
                        return new JoinableResult.Joinable(buildRewriteSequence(lazyFoundOtherSubstitutions.get(rewriteStep.substitutedTerm())), buildRewriteSequence(stepNode));
                    lazyFoundOwnSubstitutions.put(rewriteStep.substitutedTerm(), stepNode);
                }
            }
        }

        return new NewLayer(newLayer);
    }

    private static ImmutableList<RewriteStep> buildRewriteSequence(BiTreeNode<RewriteStep> node) {
        assert node != null;

        List<RewriteStep> sequence = new Stack<>();
        BiTreeNode<RewriteStep> currentNode = node;

        while (currentNode != null) {
            sequence.add(currentNode.getValue());
            currentNode = currentNode.getParent();
        }

        Collections.reverse(sequence);
        return ImmutableCreator.create(sequence);
    }
}
