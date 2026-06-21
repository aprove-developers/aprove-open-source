package aprove.runtime;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.Parameters.*;
import aprove.strategies.UserStrategies.*;

/**
 * This class is used by UI code as analogon to {@link AProVE},
 * when we want to run a processor on nodes in an existing proof tree.
 */
public class SubAprove implements ProveRunner {
    private final AProVE parent;
    private final List<BasicObligationNode> positions;

    private long timeout = 60000;
    private UserStrategy userStrategy = null;
    private StrategyExecutionHandle handle;

    public SubAprove(final AProVE parent, final List<BasicObligationNode> positions) {
        this.parent = parent;
        this.positions = positions;
    }

    @Override
    public ExecutableStrategy getResult() {
        return this.handle.getResult();
    }

    @Override
    public ObligationNode getRoot() {
        return this.parent.getRoot();
    }

    public void setTimeout(final long timeout) {
        this.timeout = timeout;
    }

    public void setUserStrategy(final UserStrategy userStrategy) {
        this.userStrategy = userStrategy;
    }

    @Override
    public boolean run() {
        final StrategyProgram strategy = this.parent.getEffectiveStrategy();
        final Map<Metadata, Object> metadata = this.parent.buildMetadata();
        this.handle = Machine.theMachine.start(this.userStrategy, strategy, this.positions, metadata);

        return AProVE.waitForHandle(this.handle, this.timeout);
    }

    public void stop() {
        this.handle.stop("GUI stop button pressed");
    }
}
