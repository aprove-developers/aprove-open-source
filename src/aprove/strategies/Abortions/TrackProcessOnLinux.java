package aprove.strategies.Abortions;

import java.io.*;
import java.net.*;
import java.util.logging.*;
import java.util.regex.*;

class TrackProcessOnLinux extends TrackProcess {
    private static final String STATPATH = "/proc/%d/stat";
    private static final long MILLIS_PER_JIFFIE = 10;

    private static Logger log = Logger.getLogger(TrackProcessOnLinux.class.getName());
    private static final Pattern parseStatLine =
        Pattern.compile("^[0-9]+ \\(.*\\) (?:\\S+\\s+){11}([0-9]+) ([0-9]+) ([0-9]+) ([0-9]+) .*$");

    private final Process process;
    private final long pid;
    private final String statpath;
    // Initial time 0: Linux has exact cpu time since process start.
    private volatile long lastCpuTime = 0;

    TrackProcessOnLinux(final Abortion abortion, final Process process) {
        super(abortion);
        this.process = process;
        this.pid = process.pid(); // since Java 9
        this.statpath = String.format(TrackProcessOnLinux.STATPATH, this.pid);
    }

    // Hack to allow us to track processes which we know only by PID,
    // not by Process object
    TrackProcessOnLinux(final Abortion abortion, final int pid) {
        super(abortion);
        this.process = null;
        this.pid = pid;
        this.statpath = String.format(TrackProcessOnLinux.STATPATH, pid);
    }

    @Override
    public void checkTime() {
        try (BufferedReader reader = new BufferedReader(new FileReader(this.statpath))) {
            String line;
            try {
                line = reader.readLine();
            } catch (final IOException hmmWhatVanished) {
                // Process probably exited just as we are checking,
                // or we hit some other kernel race
                TrackProcessOnLinux.log.log(Level.FINE, "unable to read stat line", hmmWhatVanished);
                return;
            }
            final Matcher matcher = TrackProcessOnLinux.parseStatLine.matcher(line);
            if (!matcher.matches()) {
                TrackProcessOnLinux.log.log(Level.WARNING, "weird stat line: " + line);
                return;
            }
            int newTime = 0;
            newTime += Integer.parseInt(matcher.group(1));
            newTime += Integer.parseInt(matcher.group(2));
            newTime += Integer.parseInt(matcher.group(3));
            newTime += Integer.parseInt(matcher.group(4));
            this.updateTime(newTime * TrackProcessOnLinux.MILLIS_PER_JIFFIE);
        } catch (final IOException e) {
            // Hmm... most likely, the process died...
            ProcessRegistry.deregister(this.process);
            TimeRefresher.deregister(this);
            return;
        }
    }

    @Override
    public void kill() {
        ProcessRegistry.deregister(this.process);
        if (this.process != null) {
            this.process.destroy();
        } else {
            try {
                final Socket spawner = ExternalSpawner.getSocket();
                final OutputStreamWriter writer = new OutputStreamWriter(spawner.getOutputStream());
                writer.write("kill " + this.pid + "\n");
                writer.flush();
                spawner.close();
            } catch (final IOException e) {
                TrackProcessOnLinux.log.log(Level.WARNING, "Unable to kill external process", e);
            }
        }
    }

    public static boolean isSupported() {
        // Can we read cpu time?
        BufferedReader reader;
        try {
            reader = new BufferedReader(new FileReader("/proc/self/stat"));
        } catch (final FileNotFoundException e) {
            return false;
        }
        String line;
        try {
            line = reader.readLine();
        } catch (final IOException wtf) {
            return false;
        } finally {
            try {
                reader.close();
            } catch (final IOException dontcare) {
                // Nothing we can do about it.
            }
        }
        final Matcher matcher = TrackProcessOnLinux.parseStatLine.matcher(line);
        if (!matcher.matches()) {
            return false;
        }
        return true;
    }

    protected void updateTime(final long newTime) {
        if (this.lastCpuTime != -1) {
            this.abortion.increaseTime(newTime - this.lastCpuTime);
        }
        this.lastCpuTime = newTime;
    }
}
