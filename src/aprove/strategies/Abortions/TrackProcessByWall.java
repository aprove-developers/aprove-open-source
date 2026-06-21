package aprove.strategies.Abortions;

/**
 * A basic process timer counting walltime until the process exits
 */
class TrackProcessByWall extends TrackProcess {
    private final Process process;
    private volatile long lastCpuTime;

    protected TrackProcessByWall(Abortion abortion, Process process) {
        super(abortion);
        this.process = process;
        this.lastCpuTime = System.currentTimeMillis();
    }

    @Override
    public void kill() {
        ProcessRegistry.deregister(this.process);
        this.process.destroy();
    }

    @Override
    public void checkTime() {
        if (this.isRunning()) {
            this.updateTime(System.currentTimeMillis());
        } else {
            ProcessRegistry.deregister(this.process);
            TimeRefresher.deregister(this);
        }
    }

    private void updateTime(long newTime) {
        this.abortion.increaseTime(newTime - this.lastCpuTime);
        this.lastCpuTime = newTime;
    }

    private boolean isRunning() {
        // Sun did not include a getter for UNIXProcess.hasExited,
        // probably because it does not exist on all platforms.
        // This does. Dirty hack, but works.
        try {
            this.process.exitValue();
            return false;
        } catch (IllegalThreadStateException stillRunning) {
            return true;
        }
    }
}
