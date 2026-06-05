package aprove.verification.confluence;

import aprove.prooftree.Export.Utility.Citation;
import aprove.prooftree.Export.Utility.Export_Util;
import aprove.prooftree.Obligations.BasicObligation;
import aprove.prooftree.Obligations.BasicObligationNode;
import aprove.prooftree.Proofs.Proof;
import aprove.strategies.Abortions.Abortion;
import aprove.strategies.Abortions.AbortionException;
import aprove.strategies.ExecutableStrategies.RuntimeInformation;
import aprove.verification.dpframework.BasicStructures.Rule;
import aprove.verification.dpframework.BasicStructures.TRSFunctionApplication;
import aprove.verification.dpframework.Processor;
import aprove.verification.dpframework.Result;
import aprove.verification.dpframework.ResultFactory;
import aprove.verification.oldframework.BasicStructures.FunctionSymbol;
import aprove.verification.oldframework.Logic.YNMImplication;
import aprove.verification.oldframework.Utility.FreshNameGenerator;
import aprove.verification.oldframework.Utility.VerbosityLevel;
import immutables.ImmutableCreator;

import java.util.*;
import java.util.stream.Collectors;

public class RedundantRuleProcessor implements Processor {

    public static class RedundantRuleProof extends Proof.DefaultProof {
        private final Set<Rule> newRules;

        public RedundantRuleProof(Set<Rule> newRules) {
            this.newRules = newRules;
        }

        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            return o.export("The TRS can be simplified by removing redundant rules ") +
                    o.cite(Citation.NAGELE15) +
                    o.cond_linebreak() +
                    o.export(" Continuing proof with the new rule set:") +
                    o.cond_linebreak() +
                    o.set(newRules, Export_Util.RULES);
        }
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

    private static boolean canRuleBeSimulated(Map<FunctionSymbol, Set<Rule>> currentRuleMap, FreshNameGenerator fng, Rule rule) {
        return rule.getLeft().computePossibleRewrites(currentRuleMap, fng).stream().anyMatch(step -> step.substitutedTerm().equals(rule.getRight()));
    }

    private static ConfTRSProblem removeRedundantRules(ConfTRSProblem confTRSProblem, Abortion aborter) {
        Set<Rule> rules = new LinkedHashSet<>(confTRSProblem.getRules());

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
                .flatMap(rule1 -> rules.stream()
                    .filter(rule2 -> rule1.getRight().unifies(rule2.getLeft()))
                    .map(rule2 -> Rule.create(rule1.getLeft(), rule2.getRight())))
                .collect(Collectors.toSet());
        rules.addAll(rhsRules);

        // Remove rules that others can simulate
        var incrementalRuleMap = new IncrementalRuleMap(rules);
        var fng = new FreshNameGenerator(incrementalRuleMap.getDefinedSymbols(), FreshNameGenerator.VARIABLES);
        rules.removeIf(rule -> {
            incrementalRuleMap.removeRule(rule);
            var doRemove = canRuleBeSimulated(incrementalRuleMap.getRuleMap(), fng, rule);
            if (!doRemove)
                incrementalRuleMap.addRule(rule);
            return doRemove;
        });

        // (del)
        rules.removeIf(rule -> {
            incrementalRuleMap.removeRule(rule);
            var joinTree = new TrsTermJoinTree<>(incrementalRuleMap.getRuleMap(), rule.getLeft(), rule.getRight());
            var result = joinTree.areTermsJoinable(0, 1, CriticalPairs.SearchMode.EXIT_ON_FIRST_JOIN, aborter);
            var doRemove = result instanceof JoinableResult.Joinable;
            if (!doRemove)
                incrementalRuleMap.addRule(rule);
            return doRemove;
        });

        return ConfTRSProblem.create(ImmutableCreator.create(rules));
    }
}
