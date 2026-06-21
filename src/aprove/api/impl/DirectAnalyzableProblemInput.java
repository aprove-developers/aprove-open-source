package aprove.api.impl;

import aprove.api.*;
import aprove.api.prooftree.*;
import aprove.api.prooftree.impl.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.oldframework.Input.*;

public class DirectAnalyzableProblemInput implements AnalyzableProblemInput {

    private final BasicObligation obligation;
    private final Language language;
    private final String name;

    public DirectAnalyzableProblemInput(final BasicObligation obligation,
                                        final Language language,
                                        final String name) {
        this.obligation = obligation;
        this.language = language;
        this.name = name;
    }

    @Override
    public ProofTreeBuilder newProofTreeBuilder() {
        return new ProofTreeBuilderImpl(
            (certPath, certifiable, strategy, timeout) ->
                AproveBuilder.createAproveFromObligation(obligation, language, name,
                                                         certPath, certifiable, strategy, timeout)
        );
    }
}
