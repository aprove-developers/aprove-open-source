package aprove.api.impl;

import aprove.api.*;
import aprove.api.prooftree.*;
import aprove.api.prooftree.impl.*;
import aprove.verification.oldframework.Input.*;

public class AnalyzableProblemInputImpl implements AnalyzableProblemInput {

    private final ProblemInputImpl problemInput;
    private final String annotation;

    public AnalyzableProblemInputImpl(ProblemInputImpl problemInput, String annotation) {
        this.problemInput = problemInput;
        this.annotation = annotation;
    }

    public ProblemInputImpl getProblemInput() {
        return problemInput;
    }

    @Override
    public ProofTreeBuilder newProofTreeBuilder() {
        return new ProofTreeBuilderImpl(
            (certPath, certifiable, strategy, timeout) ->
                AproveBuilder.createAprove(this, certPath, certifiable, strategy, timeout)
        );
    }

    public Input createInput() {
        Input input = problemInput.createInput();
        if (!annotation.isEmpty()) {
            input.setProtoAnnotation(annotation);
        }
        return input;
    }
}
