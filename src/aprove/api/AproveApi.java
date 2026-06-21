package aprove.api;

import java.nio.file.*;

import aprove.api.impl.*;

/**
 * This class is the entry point to the AProVE API. To get an instance, call {@link #newInstance()}.
 */
public interface AproveApi {

    public static AproveApi newInstance() {
        return new AproveApiImpl();
    }

    ProblemInput newProblemInput(Path path);

    TrsInputBuilder newTrsInput();

    PtrsInputBuilder newPtrsInput(Goal goal);
}
