package aprove.strategies.Abortions;

import java.util.logging.*;

import aprove.*;
import aprove.strategies.Util.*;

/**
 * A superclass for all jobs that processors want to submit to a threadpool.
 *
 * This class ensures that CPU time is properly accounted for,
 * uncaught exceptions are reported as for processors,
 * and that Thread.stop() is never triggered on a thread after
 * it has been returned back to the thread pool.
 * CPU time is automatically clocked to the abortion passed in the
 * constructor. Just don't invoke run() directly from the processor thread,
 * or CPU time will be counted twice.
 *
 * (In fact, processor execution is implemented via this class.)
 *
 * To do something useful, override wrappedRun(), and shortName() for logging.
 *
 * To be notified when your job terminated unexpectedly, override
 * onAborted, onKilled, or onErrord.
 * To perform final cleanup, override runFinally().
 * By default, all those methods do nothing.
 */
public abstract class PooledJob implements Runnable {
    private final static Logger log = Logger.getLogger(PooledJob.class.getName());

    private static enum ExecutionState {
        STARTING, RUNNING, KILLED, DONE
    }

    private final TrackThreadPool timeTracker;

    private ExecutionState execState = ExecutionState.STARTING;
    private ExceptionLogger exceptionLogger = null;
    private volatile Thread runnerThread = null;

    public PooledJob(Abortion abortion) {
        this.timeTracker = TrackThreadPool.createAndStart(abortion, this);
    }

    public void setExceptionLogger(final ExceptionLogger logger) {
        this.exceptionLogger = logger;
    }

    /**
     * Override to get a different name logged when Thread.stop() happens
     */
    public String longName() {
        return this.shortName();
    }

    /**
     * My name, for the logs
     */
    public abstract String shortName();

    /**
     * Do your stuff here.
     */
    protected abstract void wrappedRun() throws AbortionException;

    /**
     * Override to be called if runner terminated by throwing an AbortionException
     */
    protected void onAborted(AbortionException e) {
        // Default: do nothing.
    }

    /**
     * Override to be called if runner was forcibly killed by Thread.stop()
     */
    protected void onKilled(ThreadDeath e) {
        // Default: do nothing.
    }

    /**
     * Override to be called if runner terminated with an Error or RuntimeException
     */
    protected void onErrord(Throwable e) {
        // Default: do nothing.
    }

    /**
     * Override to be called when the runner finishes, for any reason
     */
    protected void runFinally() {
        // Default: do nothing.
    }

    // Final: Implement wrappedRun() instead, and use runFinally() if necessary
    @Override
    public final void run() {
        try {
            this.startExec();
            this.wrappedRun();
        } catch (AbortionException e) {
            PooledJob.log.log(Level.INFO, "Aborted "+this.shortName()+" with reason "+e.toString()+".\n");
            this.onAborted(e);
        } catch (ThreadDeath e) {
            PooledJob.log.log(Level.WARNING, "Aborted "+this.longName()+" with a hard timeout.\n");
            this.onKilled(e);
        } catch (Throwable e) {
            if (PooledJob.log.isLoggable(Level.WARNING)) {
                PooledJob.log.log(Level.WARNING, "Aborted "+this.shortName()+" with some error. Reason: "+e.toString()+".\n");
                for (StackTraceElement ste : e.getStackTrace()) {
                    PooledJob.log.log(Level.WARNING, "            "+ste.toString()+"\n");
                }
            }
            if (this.exceptionLogger != null) {
                this.exceptionLogger.log(e);
            }
            if (Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
                e.printStackTrace();
            }
            this.onErrord(e);
        }

        try {
            this.runFinally();
        } finally {
            this.finish();
        }
    }

    private void startExec() throws AbortionException {
        synchronized(this) {
            switch(this.execState) {
            case STARTING:
                this.execState = ExecutionState.RUNNING;
                this.runnerThread = Thread.currentThread();
                this.timeTracker.startTrackingMe();
                break;
            case KILLED:
                throw new AbortionException("Already aborted");
            case RUNNING: case DONE: default:
                assert false : "Unexpected state in startExec()";
            }
        }
    }

    private void finish() {
        this.timeTracker.stopTracking();
        synchronized(this) {
            switch(this.execState) {
            case RUNNING:
                this.execState = ExecutionState.DONE;
                this.runnerThread = null;
                break;
            case KILLED:
                // If we get here, we're either about to receive a ThreadDeath
                // or caught one earlier. In any case, don't trust this thread
                // anymore and terminate it.
                throw new ThreadDeath();
            case STARTING: case DONE: default:
                assert false : "Unexpected executor state in finish()";
            }
        }
    }

    public void kill() {
        synchronized(this) {
            switch(this.execState) {
            case STARTING:
                this.execState = ExecutionState.KILLED;
                break;
            case RUNNING:
                this.execState = ExecutionState.KILLED;
                TrackThread.logThreadStop(this.runnerThread, this.longName());
                // Thread.stop() always throws since JDK 20 and is gone in JDK 26
                this.runnerThread.interrupt();
                break;
            case DONE:
                // nothing to do
                break;
            case KILLED: default:
                assert false : "Unexpected executor state in kill()";
            }
        }
    }
}