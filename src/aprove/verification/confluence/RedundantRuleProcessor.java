package aprove.verification.confluence;

import aprove.prooftree.Obligations.BasicObligation;
import aprove.prooftree.Obligations.BasicObligationNode;
import aprove.strategies.Abortions.Abortion;
import aprove.strategies.Abortions.AbortionException;
import aprove.strategies.Annotations.ParamsViaArgumentObject;
import aprove.strategies.ExecutableStrategies.RuntimeInformation;
import aprove.verification.dpframework.BasicStructures.Rule;
import aprove.verification.dpframework.BasicStructures.TRSFunctionApplication;
import aprove.verification.dpframework.Processor;
import aprove.verification.dpframework.Result;
import aprove.verification.dpframework.ResultFactory;
import aprove.verification.oldframework.BasicStructures.FunctionSymbol;
import aprove.verification.oldframework.Logic.YNMImplication;
import aprove.verification.oldframework.Utility.FreshNameGenerator;
import immutables.ImmutableCreator;

import java.util.*;
import java.util.stream.Collectors;

public class RedundantRuleProcessor implements Processor {
    private final Arguments arguments;

    @ParamsViaArgumentObject
    public RedundantRuleProcessor(Arguments arguments) {
        this.arguments = arguments;
    }

    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        var confTRSProblem = (ConfTRSProblem) obl;

        var newConfTRSProblem = removeRedundantRules(confTRSProblem, aborter);

        return ResultFactory.provedAnd(List.of(newConfTRSProblem), YNMImplication.SOUND, new RedundantRuleProof(newConfTRSProblem.getRules()));
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof ConfTRSProblem;
    }

    public static class Arguments {
        /** Maximum number of rewrite steps searched when checking whether a rule's left side reaches its right side. **/
        public int ReachabilityLimit = 6;
    }

    private static boolean canRuleBeSimulated(Map<FunctionSymbol, ? extends Set<Rule>> currentRuleMap, FreshNameGenerator fng, Rule rule) {
        return rule.getLeft().computePossibleRewrites(currentRuleMap, fng).stream().anyMatch(step -> step.substitutedTerm().equals(rule.getRight()));
    }

    private ConfTRSProblem removeRedundantRules(ConfTRSProblem confTRSProblem, Abortion aborter) {
        Set<Rule> rules = new LinkedHashSet<>(confTRSProblem.getRules());
        var incrementalRuleMap = new IncrementalRuleMap(rules);

        // (js)
        var criticalPairs = confTRSProblem.getCriticalPairs();
        criticalPairs.ensureStrongJoinabilityIsDetermined(aborter);
        var stronglyJoinable = criticalPairs.getFoundJoinable();
        for (var entry : stronglyJoinable.entrySet()) {
            var cpInfo = entry.getKey();
            var rewriteSequences = entry.getValue();
            if (!(cpInfo.s() instanceof TRSFunctionApplication) || !(cpInfo.t() instanceof TRSFunctionApplication))
                continue;
            var r1 = Rule.create((TRSFunctionApplication) cpInfo.s(), rewriteSequences.x.getLast().substitutedTerm());
            var r2 = Rule.create((TRSFunctionApplication) cpInfo.t(), rewriteSequences.y.getLast().substitutedTerm());

            rules.add(r2);
            rules.add(r1);
        }

        // (rhs)
        Set<Rule> rhsRules = rules.stream()
                .flatMap(r -> r.getRight()
                        .rewrite(incrementalRuleMap.toImmutable())
                        .stream()
                        .map(rewrite -> Rule.create(r.getLeft(), rewrite)))
                .collect(Collectors.toSet());
        rules.addAll(rhsRules);

        // Remove rules that others can simulate
        var fng = new FreshNameGenerator(incrementalRuleMap.getDefinedSymbols(), FreshNameGenerator.VARIABLES);
        rules.removeIf(rule -> {
            incrementalRuleMap.removeRule(rule);
            var doRemove = canRuleBeSimulated(incrementalRuleMap.toImmutable(), fng, rule);
            if (!doRemove)
                incrementalRuleMap.addRule(rule);
            return doRemove;
        });

        // (del) A rule l -> r is redundant and may be removed only if l can still reach r in the
        // remaining TRS (l ->* r). This preserves ->* and hence confluence [NAGELE15].
        rules.removeIf(rule -> {
            incrementalRuleMap.removeRule(rule);
            var joinTree = new TrsTermJoinTree(incrementalRuleMap.toImmutable(), rule.getLeft(), rule.getRight());
            var result = joinTree.areTermsJoinable(0, arguments.ReachabilityLimit, CriticalPairs.SearchMode.EXIT_ON_FIRST_JOIN, aborter);
            var doRemove = result instanceof JoinableResult.Joinable;
            if (!doRemove)
                incrementalRuleMap.addRule(rule);
            return doRemove;
        });

        return ConfTRSProblem.create(ImmutableCreator.create(rules));
    }
}
