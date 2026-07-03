package aprove.api;

import java.util.*;

import aprove.api.impl.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.Input.*;
import immutables.*;

public final class TrsInputBuilder {

    private final Set<Rule> rules = new LinkedHashSet<>();
    private String name = "";

    public TrsInputBuilder() {}

    public TrsInputBuilder add(final Rule rule) {
        rules.add(rule);
        return this;
    }

    public TrsInputBuilder name(final String name) {
        this.name = name;
        return this;
    }

    public AnalyzableProblemInput build() {
        QTRSProblem obligation = QTRSProblem.create(ImmutableCreator.create(new LinkedHashSet<>(rules)));
        return new DirectAnalyzableProblemInput(obligation, Language.QTRS, name);
    }
}
