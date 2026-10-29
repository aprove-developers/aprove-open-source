package aprove.strategies.Abortions;

class TrackThreadCustom extends TrackThread {
    private final Thread thread;

    TrackThreadCustom(Abortion parent, Thread thread) {
        super(parent);
        this.thread = thread;
    }

    @Override
    protected Thread getThread() {
        if (this.thread.getState() == Thread.State.TERMINATED) {
            TimeRefresher.deregister(this);
        }
        return this.thread;
    }

    @Override
    public void kill() {
        if (this.thread.getState() == Thread.State.TERMINATED) {
            return;
        }
        TrackThread.logThreadStop(this.thread, this.thread.getName());
        this.thread.interrupt();
    }

}
