package aprove.strategies.Abortions;

import java.util.*;
import java.util.concurrent.*;

/**
 * Global registry of external processes spawned by AProVE.
 *
 * Every process tracked via {@link TrackerFactory#process} is registered here.
 * A JVM shutdown hook forcibly destroys any process that is still alive when the
 * JVM exits — covering both normal completion and abrupt termination.
 */
final class ProcessRegistry {

    private static final Set<Process> running =
        Collections.newSetFromMap(new ConcurrentHashMap<>());

    static {
        Runtime.getRuntime().addShutdownHook(new Thread(() -> {
            for (Process p : running) {
                p.destroyForcibly();
            }
        }, "aprove-process-reaper"));
    }

    static void register(final Process process) {
        running.add(process);
    }

    static void deregister(final Process process) {
        if (process != null) {
            running.remove(process);
        }
    }

    private ProcessRegistry() {}
}
