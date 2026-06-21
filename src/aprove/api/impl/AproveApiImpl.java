package aprove.api.impl;

import java.nio.file.*;
import java.util.*;

import aprove.api.*;

public class AproveApiImpl implements AproveApi {

    @Override
    public ProblemInput newProblemInput(Path path) {
        Objects.requireNonNull(path);
        return ProblemInputImpl.from(path);
    }

    @Override
    public TrsInputBuilder newTrsInput() {
        return new TrsInputBuilder();
    }

    @Override
    public PtrsInputBuilder newPtrsInput(Goal goal) {
        Objects.requireNonNull(goal);
        return new PtrsInputBuilder(goal);
    }
}
