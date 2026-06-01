package aprove.verification.confluence;


import aprove.verification.dpframework.BasicStructures.Rule;
import aprove.verification.oldframework.BasicStructures.FunctionSymbol;
import immutables.ImmutableCreator;
import immutables.ImmutableMap;
import immutables.ImmutableSet;

import java.util.LinkedHashMap;
import java.util.LinkedHashSet;
import java.util.Map;
import java.util.Set;
import java.util.stream.Collectors;

public class IncrementalRuleMap {
    private final Map<FunctionSymbol, Set<Rule>> ruleMap;

    public IncrementalRuleMap(Set<Rule> initialRules) {
        this.ruleMap = new LinkedHashMap<>();
        for (final var rule : initialRules)
            addToRuleMap(rule);
    }

    public void addRule(Rule rule) {
        addToRuleMap(rule);
    }

    public void removeRule(Rule rule) {
        final FunctionSymbol f = rule.getRootSymbol();
        var fRules = ruleMap.getOrDefault(f, null);
        if (fRules != null)
            fRules.remove(rule);
    }

    public Map<FunctionSymbol, Set<Rule>> getRuleMap() {
        return ruleMap;
    }

    public Set<FunctionSymbol> getDefinedSymbols() {
        return ruleMap.keySet();
    }

    public ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> toImmutable() {
        var innerImmutable = ruleMap.entrySet().stream().collect(Collectors.toMap(
                Map.Entry::getKey,
                entry -> ImmutableCreator.create(entry.getValue())
        ));
        return ImmutableCreator.create(innerImmutable);
    }

    private void addToRuleMap(Rule rule) {
        final FunctionSymbol f = rule.getRootSymbol();
        Set<Rule> fRules = ruleMap.computeIfAbsent(f, _ -> new LinkedHashSet<>());
        fRules.add(rule);
    }
}
