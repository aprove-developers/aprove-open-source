package aprove.api;

import java.util.*;

import aprove.api.impl.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;

public final class PtrsInputBuilder {

    private final Goal goal;
    private final Set<ProbabilisticRule> rules = new LinkedHashSet<>();
    private String name = "";

    public PtrsInputBuilder(final Goal goal) {
        this.goal = goal;
    }

    public PtrsInputBuilder add(final ProbabilisticRule rule) {
        rules.add(rule);
        return this;
    }

    public PtrsInputBuilder name(final String name) {
        this.name = name;
        return this;
    }

    public AnalyzableProblemInput build() {
        ProbabilisticTerminationResult target = toResult(goal);
        PTRSProblem obligation = new PTRSProblem(rules, RewriteStrategy.FULL, target, false);
        return new DirectAnalyzableProblemInput(obligation, Language.PTRS, name);
    }

    private static ProbabilisticTerminationResult toResult(final Goal g) {
        switch (g) {
            case AST:         return ProbabilisticTerminationResult.AST;
            case SAST:        return ProbabilisticTerminationResult.SAST;
            case TERMINATION: return ProbabilisticTerminationResult.certainTermination;
            default: throw new IllegalArgumentException("Unknown goal: " + g);
        }
    }
}
