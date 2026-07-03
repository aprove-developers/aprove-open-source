package aprove.strategies.Abortions;

/**
 * Utility class for tracking CPU time.
 *
 * Use one of the methods in here to start tracking of something.
 *
 * All objects will subscribe to the passed abortion and kill the
 * tracked thing as soon as the abortion fires.
 */
public abstract class TrackerFactory {
    /**
     * Tracks a custom Thread object.
     *
     * The thread is given some grace time before being terminated with
     * a Thread.stop(), however you should try to abort cleanly before
     * that happens.
     *
     * Whenever possible, use a {@link aprove.strategies.Abortions.PooledJob}
     * and the thread pool instead of this method.
     */
    public static TimeTracker customThread(Abortion abortion, Thread thread) {
        TrackThread result = new TrackThreadCustom(abortion, thread);
        result.start();
        return result;
    }

    /**
     * Tracks a started Process.
     *
     * Should be called anytime you start an external process to do
     * some computation.
     *
     * Implementation note: Does not properly track CPU time of shell scripts!
     * (due to children remaining untracked)
     */
    public static TimeTracker process(Abortion abortion, Process process) {
        ProcessRegistry.register(process);
        TrackProcess result = TrackProcess.create(process, abortion);
        result.start();
        return result;
    }

    /**
     * Tracks an arbitrary PID
     *
     * Try to use {@link #process(Abortion, Process)} instead. This method
     * may be necessary if you use the external process spawner service.
     */
    public static void processByPID(Abortion aborter, int pid) {
        TrackProcess result = new TrackProcessOnLinux(aborter, pid);
    }
}
