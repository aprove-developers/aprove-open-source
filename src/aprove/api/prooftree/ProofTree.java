package aprove.api.prooftree;

import java.util.concurrent.*;

/**
 * The proof tree contains information about each step of the analysis.
 * Use this class to run an analysis that provides live updates for each change to the proof tree.
 * This class is mainly used for the GUI, so the user gets feedback not only after the analysis is done, but right from the start of the analysis.
 */
public interface ProofTree {

    void run(ProofResultHandler proofResultHandler);

    ProofTreeNode getRoot();

    ProofTreeOperationManager getOperationManager();

    /**
     * Runs the analysis asynchronously and returns a {@link CompletableFuture} that completes with
     * the result string (e.g. {@code "YES"}, {@code "NO"}, {@code "MAYBE"}) when the analysis
     * finishes. On timeout the future completes with {@code "MAYBE"}. On error the future completes
     * exceptionally with the underlying exception.
     *
     * <p>This is a convenience alternative to {@link #run(ProofResultHandler)} that removes the
     * need to manage a {@link java.util.concurrent.CountDownLatch} manually.
     *
     * <pre>{@code
     * String result = tree.runAsync().get();
     * }</pre>
     */
    default CompletableFuture<String> runAsync() {
        CompletableFuture<String> future = new CompletableFuture<>();
        run(new ProofResultHandler() {
            @Override public void onRun(ProofTreeOperationManager m) {}
            @Override public void onSuccess(ProofTreeOperationManager m, String msg) { future.complete(msg); }
            @Override public void onTimeout(ProofTreeOperationManager m) { future.complete("MAYBE"); }
            @Override public void onError(ProofTreeOperationManager m, Exception e) { future.completeExceptionally(e); }
        });
        return future;
    }
}
