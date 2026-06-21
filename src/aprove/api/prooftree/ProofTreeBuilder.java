package aprove.api.prooftree;

import java.nio.file.*;
import java.util.*;

/**
 * Creates a new {@link ProofTree}.
 */
public interface ProofTreeBuilder {

    BeforeOnlyCertifiableTechniquesIfPossible onlineCertificationPath(Optional<Path> path);

    public static interface BeforeOnlyCertifiableTechniquesIfPossible {

        BeforeStrategy onlyCertifiableTechniquesIfPossible(boolean condition);
    }

    public static interface BeforeStrategy {

        BeforeTimeout strategy(Optional<Strategy> strategy);
    }

    public static interface BeforeTimeout {

        BeforeListener timeout(Timeout timeout);
    }

    public static interface BeforeListener extends BeforeConstruct {

        BeforeConstruct listener(ProofTreeListener proofTreeListener);
    }

    public static interface BeforeConstruct {

        ProofTree construct() throws ProofTreeInstantiationException;
    }
}
