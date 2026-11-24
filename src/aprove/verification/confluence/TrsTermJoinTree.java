package aprove.verification.confluence;

import aprove.strategies.Abortions.Abortion;
import aprove.verification.confluence.Utility.CriticalPairInfo;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.FunctionSymbol;
import aprove.verification.oldframework.Utility.GenericStructures.Wrapper;
import immutables.ImmutableCreator;
import immutables.ImmutableList;

import java.util.*;

/**
 * Dynamically builds up two trees breadth-first and tests for a common reduct for two given terms.
 */
public class TrsTermJoinTree {
    private final Map<FunctionSymbol, ? extends Set<Rule>> rules;
    private final CriticalPairInfo cpInfo;
    private final TRSTerm s;
    private final TRSTerm t;
    private final Map<TRSTerm, ImmutableList<RewriteStep>> normalFormCache;
    private final HashMap<TRSTerm, PathNode> sReached = new HashMap<>();
    private final HashMap<TRSTerm, PathNode> tReached = new HashMap<>();
    private List<PathNode> sLastLayer = new ArrayList<>();
    private List<PathNode> tLastLayer = new ArrayList<>();
    private final Wrapper<ImmutableList<RewriteStep>> sNormalForm = new Wrapper<>(null);
    private final Wrapper<ImmutableList<RewriteStep>> tNormalForm = new Wrapper<>(null);

    private record PathNode(RewriteStep step, PathNode parent) {
        TRSTerm substitutedTerm() {
            return step.substitutedTerm();
        }
    }

    public TrsTermJoinTree(Map<FunctionSymbol, ? extends Set<Rule>> rules, CriticalPairInfo cpInfo, Map<TRSTerm, ImmutableList<RewriteStep>> normalFormCache) {
        this(rules, cpInfo.s(), cpInfo.t(), new PathNode(new RewriteStep(cpInfo.divergence(), Position.EPSILON, cpInfo.sRule(), cpInfo.s()), null), new PathNode(new RewriteStep(cpInfo.divergence(), Position.EPSILON, cpInfo.tRule(), cpInfo.t()), null), normalFormCache, cpInfo);
    }

    public TrsTermJoinTree(Map<FunctionSymbol, ? extends Set<Rule>> rules, TRSTerm s, TRSTerm t) {
        this(rules, s, t, new PathNode(new RewriteStep(null, null, null, s), null), new PathNode(new RewriteStep(null, null, null, t), null), new HashMap<>(), null);
    }

    private TrsTermJoinTree(Map<FunctionSymbol, ? extends Set<Rule>> rules, TRSTerm s, TRSTerm t, PathNode sRoot, PathNode tRoot, Map<TRSTerm, ImmutableList<RewriteStep>> normalFormCache, CriticalPairInfo cpInfo) {
        this.rules = rules;
        this.cpInfo = cpInfo;
        this.s = s;
        this.t = t;
        this.normalFormCache = normalFormCache;
        this.sLastLayer.add(sRoot);
        this.tLastLayer.add(tRoot);
        this.sReached.put(s, sRoot);
        this.tReached.put(t, tRoot);
    }

    JoinableResult areTermsJoinable(int start, int limit, CriticalPairs.SearchMode searchMode, Abortion aborter) {
        if (s.equals(t))
            return new JoinableResult.Joinable(ImmutableCreator.create(Collections.emptyList()), ImmutableCreator.create(Collections.emptyList()));

        if (start >= limit)
            return new JoinableResult.Maybe();

        if (normalFormCache != null) {
            ImmutableList<RewriteStep> leftNF = normalFormCache.get(s);
            ImmutableList<RewriteStep> rightNF = normalFormCache.get(t);
            if (leftNF != null && rightNF != null && !leftNF.getLast().substitutedTerm().equals(rightNF.getLast().substitutedTerm()))
                return new JoinableResult.WcrCounterExample.NonConfluent(leftNF, rightNF);
        }

        // TODO: actually implement start argument
        for (int i = 0; i < limit; i++) {
            var sResult = buildTreeLayer(s, sLastLayer, sReached, tReached, sNormalForm, searchMode, aborter);
            if (!(sResult instanceof NewLayer(List<PathNode> sNewLayer)))
                return sResult;
            sLastLayer = sNewLayer;

            var tResult = buildTreeLayer(t, tLastLayer, tReached, sReached, tNormalForm, searchMode, aborter);
            if (!(tResult instanceof NewLayer(List<PathNode> tNewLayer)))
                return tResult;
            tLastLayer = tNewLayer;

            // TODO: Implement searchMode. At this point, we would need to check if we found a join term and return a JoinableResult.Joinable
            if (sNewLayer.isEmpty() && tNewLayer.isEmpty())
                return new JoinableResult.WcrCounterExample.NonJoinable(cpInfo);
        }

        return new JoinableResult.Maybe();
    }

    record NewLayer(List<PathNode> newLayer) implements JoinableResult {}

    private JoinableResult buildTreeLayer(
            TRSTerm root,
            List<PathNode> lastLayer,
            HashMap<TRSTerm, PathNode> ownReached,
            HashMap<TRSTerm, PathNode> otherReached,
            Wrapper<ImmutableList<RewriteStep>> foundNormalForm,
            CriticalPairs.SearchMode searchMode,
            Abortion aborter) {

        List<PathNode> newLayer = new ArrayList<>();
        for (PathNode node : lastLayer) {
            aborter.checkAbortion();
            var possibleRewrites = node.substitutedTerm().computePossibleRewrites(rules);

            // No further rewrites possible, we found a normal form
            if (possibleRewrites.isEmpty()) {
                // Check if we previously found a normal form.
                // If so, the TRS cannot be confluent
                if (foundNormalForm.x == null) {
                    foundNormalForm.x = buildRewriteSequence(node);
                    if (normalFormCache != null)
                        normalFormCache.putIfAbsent(root, foundNormalForm.x);
                } else if (!foundNormalForm.x.getLast().substitutedTerm().equals(node.substitutedTerm())) {
                    return new JoinableResult.WcrCounterExample.NonConfluent(foundNormalForm.x, buildRewriteSequence(node));
                }
                continue;
            }

            // Otherwise, expand every successor term that has not been reached before.
            // Since the search is breadth-first, the first path to a term is also a shortest one,
            // so terms reached again need not be expanded a second time.
            for (final RewriteStep rewriteStep : possibleRewrites) {
                TRSTerm term = rewriteStep.substitutedTerm();
                if (ownReached.containsKey(term))
                    continue;

                PathNode stepNode = new PathNode(rewriteStep, node);
                PathNode otherNode = otherReached.get(term);
                if (otherNode != null)
                    return new JoinableResult.Joinable(buildRewriteSequence(otherNode), buildRewriteSequence(stepNode));

                ownReached.put(term, stepNode);
                newLayer.add(stepNode);
            }
        }

        return new NewLayer(newLayer);
    }

    private static ImmutableList<RewriteStep> buildRewriteSequence(PathNode node) {
        assert node != null;

        int length = 0;
        for (PathNode current = node; current != null; current = current.parent())
            length++;

        RewriteStep[] sequence = new RewriteStep[length];
        for (PathNode current = node; current != null; current = current.parent())
            sequence[--length] = current.step();

        return ImmutableCreator.create(Arrays.asList(sequence));
    }
}
