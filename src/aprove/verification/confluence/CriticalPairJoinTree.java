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

public class CriticalPairJoinTree<T extends GeneralizedRule> {
    private final CriticalPairInfo criticalPairInfo;
    private final Map<FunctionSymbol, ? extends Set<? extends T>> rules;
    private Set<BiTreeNode<RewriteStep>> sLastLayer = new LinkedHashSet<>();
    private Set<BiTreeNode<RewriteStep>> tLastLayer = new LinkedHashSet<>();
    private final Map<TRSTerm, ImmutableList<RewriteStep>> normalFormCache;
    private final HashMap<TRSTerm, BiTreeNode<RewriteStep>> sLazySubstitutions = new HashMap<>();
    private final HashMap<TRSTerm, BiTreeNode<RewriteStep>> tLazySubstitutions = new HashMap<>();
    private final FreshNameGenerator freshNames = new FreshNameGenerator(FreshNameGenerator.VARIABLES);
    private ImmutableList<RewriteStep> foundNormalForm;

    public CriticalPairJoinTree(Map<FunctionSymbol, ? extends Set<? extends T>> rules, CriticalPairInfo criticalPairInfo, Map<TRSTerm, ImmutableList<RewriteStep>> normalFormCache) {
        this.rules = rules;
        this.criticalPairInfo = criticalPairInfo;
        BiTreeNode<RewriteStep> sTree = new BiTreeNode<>(new RewriteStep(criticalPairInfo.divergence(), Position.EPSILON, criticalPairInfo.sRule(), criticalPairInfo.s()));
        BiTreeNode<RewriteStep> tTree = new BiTreeNode<>(new RewriteStep(criticalPairInfo.divergence(), Position.EPSILON, criticalPairInfo.tRule(), criticalPairInfo.t()));
        this.sLastLayer.add(sTree);
        this.tLastLayer.add(tTree);
        this.normalFormCache = normalFormCache;
        this.sLazySubstitutions.put(criticalPairInfo.s(), sTree);
        this.tLazySubstitutions.put(criticalPairInfo.t(), tTree);
        freshNames.lockNames(CollectionUtils.getNames(criticalPairInfo.s().getVariables()));
        freshNames.lockNames(CollectionUtils.getNames(criticalPairInfo.t().getVariables()));
    }

    JoinableResult isCriticalPairJoinable(int start, int limit, CriticalPairs.SearchMode searchMode, Abortion aborter) {
        if (start >= limit)
            return new JoinableResult.Maybe();

        if (normalFormCache != null) {
            ImmutableList<RewriteStep> leftNF = normalFormCache.get(criticalPairInfo.s());
            ImmutableList<RewriteStep> rightNF = normalFormCache.get(criticalPairInfo.t());
            if (leftNF != null && rightNF != null && leftNF.size() > 1 && rightNF.size() > 1 && !leftNF.getLast().substitutedTerm().equals(rightNF.getLast().substitutedTerm()))
                return new JoinableResult.WcrCounterExample.NonConfluent(leftNF, rightNF);
            if (leftNF != null && leftNF.size() > 1)
                foundNormalForm = leftNF;
            else if (rightNF != null && rightNF.size() > 1)
                foundNormalForm = rightNF;
        }

        // TODO: actually implement start argument
        for (int i = 0; i < limit; i++) {
            JoinableResult sResult = buildTreeLayer(criticalPairInfo.s(), sLastLayer, sLazySubstitutions, tLazySubstitutions, searchMode, aborter);
            if (!(sResult instanceof NewLayer(Set<BiTreeNode<RewriteStep>> sNewLayer)))
                return sResult;
            sLastLayer = sNewLayer;

            var tResult = buildTreeLayer(criticalPairInfo.t(), tLastLayer, tLazySubstitutions, sLazySubstitutions, searchMode, aborter);
            if (!(tResult instanceof NewLayer(Set<BiTreeNode<RewriteStep>> tNewLayer)))
                return tResult;
            tLastLayer = tNewLayer;

            // TODO: Implement searchMode. At this point, we would need to check if we found a join term and return a JoinableResult.Joinable
            if (sNewLayer.isEmpty() && tNewLayer.isEmpty())
                return new JoinableResult.WcrCounterExample.NonJoinable(criticalPairInfo);
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
        //return new RewriteSequence(sequence.getFirst().substitutedTerm(), sequence.getLast().substitutedTerm(), ImmutableCreator.create(sequence));
    }
}
