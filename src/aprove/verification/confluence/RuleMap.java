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

/**
 * A class holding an {@link ImmutableSet} mapping root symbols to their rules.
 * @param ruleMap The resulting rule map.
 */
public record RuleMap(ImmutableMap<FunctionSymbol, ImmutableSet<Rule>> ruleMap) {
    public RuleMap(Set<Rule> initialRules) {
        var map = new LinkedHashMap<FunctionSymbol, Set<Rule>>();
        for (final var rule : initialRules) {
            final FunctionSymbol f = rule.getRootSymbol();
            Set<Rule> fRules = map.computeIfAbsent(f, _ -> new LinkedHashSet<>());
            fRules.add(rule);
        }

        var innerImmutable = map.entrySet().stream().collect(Collectors.toMap(
                Map.Entry::getKey,
                entry -> ImmutableCreator.create(entry.getValue())
        ));
        this(ImmutableCreator.create(innerImmutable));
    }

    public ImmutableSet<FunctionSymbol> getDefinedSymbols() {
        return ImmutableCreator.create(ruleMap.keySet());
    }
}
