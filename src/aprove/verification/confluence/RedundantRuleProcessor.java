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

    /** Maximum number of rewrite steps searched when checking whether a rule's left side reaches its right side. */
    private static final int REACHABILITY_LIMIT = 8;

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

        if(newConfTRSProblem.equals(confTRSProblem)){
            return ResultFactory.unsuccessful("No rules have been removed.");
        }

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
                        .rewrite(incrementalRuleMap.getRuleMap())
                        .stream()
                        .map(rewrite -> Rule.create(r.getLeft(), rewrite)))
                .collect(Collectors.toSet());
        rules.addAll(rhsRules);

        // Remove rules that others can simulate
        var fng = new FreshNameGenerator(incrementalRuleMap.getDefinedSymbols(), FreshNameGenerator.VARIABLES);
        rules.removeIf(rule -> {
            incrementalRuleMap.removeRule(rule);
            var doRemove = canRuleBeSimulated(incrementalRuleMap.getRuleMap(), fng, rule);
            if (!doRemove)
                incrementalRuleMap.addRule(rule);
            return doRemove;
        });

        // (del) A rule l -> r is redundant and may be removed only if l can still reach r in the
        // remaining TRS (l ->* r). This preserves ->* and hence confluence [NAGELE15]. Note that mere
        // joinability (l ->* u <-* r) is NOT sufficient: it can drop a rule whose left side can no
        // longer reach its right side, turning a non-confluent TRS into a confluent one.
        rules.removeIf(rule -> {
            incrementalRuleMap.removeRule(rule);
            var joinTree = new TrsTermJoinTree(incrementalRuleMap.getRuleMap(), rule.getLeft(), rule.getRight());
            var result = joinTree.isRightTermReachable(REACHABILITY_LIMIT, aborter);
            var doRemove = result instanceof JoinableResult.Joinable;
            if (!doRemove)
                incrementalRuleMap.addRule(rule);
            return doRemove;
        });

        return ConfTRSProblem.create(ImmutableCreator.create(rules));
    }
}
