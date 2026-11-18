package aprove.verification.confluence;

import aprove.verification.confluence.Utility.CriticalPairInfo;
import aprove.verification.dpframework.BasicStructures.GeneralizedRule;
import aprove.verification.oldframework.BasicStructures.FunctionSymbol;
import immutables.ImmutableList;

/**
 * A common interface for each result type that may be produced by the @{@link TrsTermJoinTree}.
 */
sealed interface JoinableResult permits TrsTermJoinTree.NewLayer, JoinableResult.Joinable, JoinableResult.Maybe, JoinableResult.NonConfluent, JoinableResult.WcrCounterExample {
    record Joinable(ImmutableList<RewriteStep> leftSequence, ImmutableList<RewriteStep> rightSequence) implements JoinableResult {}
    record NonConfluent(ImmutableList<RewriteStep> leftNormalForm, ImmutableList<RewriteStep> rightNormalForm) implements JoinableResult {}
    record Maybe() implements JoinableResult {}

    sealed interface WcrCounterExample extends JoinableResult {
        record InvalidRootSymbol(GeneralizedRule sRule, GeneralizedRule tRule, FunctionSymbol f, FunctionSymbol g) implements WcrCounterExample { }
        record NonJoinable(CriticalPairInfo criticalPairInfo) implements WcrCounterExample {}
    }
}
