package aprove.runtime;

import aprove.prooftree.Obligations.*;
import aprove.strategies.ExecutableStrategies.*;

/**
 * Common superinterface of {@link AProVE} and {@link SubAprove},
 * contains methods to run the contained machine and see what it did
 */
public interface ProveRunner {
    public boolean run();

    public ExecutableStrategy getResult();

    public ObligationNode getRoot();
}
