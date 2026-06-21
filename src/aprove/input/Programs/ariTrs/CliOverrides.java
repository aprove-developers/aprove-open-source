package aprove.input.Programs.ariTrs;

/**
 * Thread-local container for CLI overrides of declarations found in .ari files.
 * Set in Main before running AProVE; read and cleared by the ariTrs Translator.
 */
public final class CliOverrides {

    private static final ThreadLocal<CliOverrides> current = new ThreadLocal<>();

    /** One of: ast, sast, termination, complexity, confluence, infeasibility, past. Null = no override. */
    public final String goal;
    /** One of: innermost, outermost, full. Null = no override. */
    public final String rewriteStrategy;
    /** One of: basic, all. Null = no override. */
    public final String startTerm;

    private CliOverrides(final String goal, final String rewriteStrategy, final String startTerm) {
        this.goal = goal;
        this.rewriteStrategy = rewriteStrategy;
        this.startTerm = startTerm;
    }

    public static void set(final String goal, final String rewriteStrategy, final String startTerm) {
        if (goal != null || rewriteStrategy != null || startTerm != null) {
            current.set(new CliOverrides(goal, rewriteStrategy, startTerm));
        }
    }

    public static CliOverrides get() {
        return current.get();
    }

    public static void clear() {
        current.remove();
    }
}
