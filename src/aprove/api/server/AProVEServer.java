package aprove.api.server;

import java.io.*;
import java.nio.file.*;
import java.util.*;
import java.util.concurrent.*;
import java.util.logging.*;

import org.json.*;

import aprove.api.impl.*;
import aprove.api.prooftree.*;
import aprove.api.prooftree.impl.*;
import aprove.input.Programs.ariTrs.*;

/**
 * Line-delimited JSON daemon.
 *
 * Reads one JSON request per line from stdin, writes one JSON response per
 * line to stdout.  Logs go to stderr so they never contaminate the JSON stream.
 *
 * Request fields:
 *   file            (required) path to the problem file
 *   timeout         (optional, ms, default 60000)
 *   rewriteStrategy (optional) "innermost" | "outermost" | "full"
 *   goal            (optional) "ast" | "sast" | "termination"
 *   name            (optional) display name (defaults to filename)
 *   cert            (optional, bool) produce a CPF3 certificate; default false
 *
 * Response fields:
 *   name, result, time (ms), timeout (bool), error, cpf, proofTree (array)
 *
 * Each proofTree entry:
 *   index, parentIndex, obligationName, obligationPlain,
 *   processorName, implication, proof
 */
public class AProVEServer {

    private static final String CPF_CONVERTER =
        Optional.ofNullable(System.getenv("CPF_CONVERTER"))
                .orElse("/opt/bundle/cpfconverter/cpf2_to_3.sh");

    public static void main(String[] args) throws IOException {
        redirectLoggingToStderr();

        BufferedReader in = new BufferedReader(new InputStreamReader(System.in));
        PrintStream out = System.out;

        String line;
        while ((line = in.readLine()) != null) {
            if (line.isBlank()) continue;
            out.println(processLine(line));
            out.flush();
        }
    }

    private static String processLine(String line) {
        try {
            return analyze(new JSONObject(line)).toString();
        } catch (JSONException e) {
            return errorResponse("malformed JSON: " + e.getMessage());
        } catch (Exception e) {
            return errorResponse(e.getMessage() != null ? e.getMessage() : e.getClass().getName());
        }
    }

    private static JSONObject analyze(JSONObject req) throws Exception {
        Path path = Paths.get(req.getString("file"));
        long timeout = req.has("timeout") ? req.getLong("timeout") : 60_000L;
        String name = req.has("name") ? req.getString("name") : path.getFileName().toString();
        boolean cert = req.has("cert") && req.getBoolean("cert");

        // "innermost" | "outermost" | "full" → CliOverrides
        String cliStrategy = req.has("rewriteStrategy") ? req.getString("rewriteStrategy").toLowerCase() : null;
        String cliGoal = req.has("goal") ? req.getString("goal").toLowerCase() : null;

        String filename = path.getFileName().toString();
        String ext = filename.contains(".") ? filename.substring(filename.lastIndexOf('.') + 1) : "";
        ProblemInputImpl problemInput = new ProblemInputImpl(path, ext);
        AnalyzableProblemInputImpl analyzable = new AnalyzableProblemInputImpl(problemInput, "");

        // Inject CliOverrides inside the factory lambda — runs synchronously in construct(),
        // which is in the calling thread, so thread-local propagation works correctly.
        AproveBuilder.AProVEFactory factory = (certPath, certifiable, strategy, tm) -> {
            CliOverrides.set(cliGoal, cliStrategy, null);
            try {
                return AproveBuilder.createAprove(analyzable, certPath, certifiable, strategy, tm);
            } finally {
                CliOverrides.clear();
            }
        };

        ServerProofListener listener = new ServerProofListener();
        long start = System.currentTimeMillis();

        ProofTree tree = new ProofTreeBuilderImpl(factory)
            .onlineCertificationPath(Optional.empty())
            .onlyCertifiableTechniquesIfPossible(cert)
            .strategy(Optional.empty())
            .timeout(Timeout.positiveOrInfinite((int) Math.min(timeout, Integer.MAX_VALUE)))
            .listener(listener)
            .construct();

        boolean timedOut = false;
        String result;
        try {
            result = tree.runAsync().get(timeout + 5_000L, TimeUnit.MILLISECONDS);
        } catch (TimeoutException e) {
            result = "MAYBE";
            timedOut = true;
        } catch (ExecutionException e) {
            throw e.getCause() instanceof Exception ? (Exception) e.getCause() : e;
        }
        long elapsed = System.currentTimeMillis() - start;

        String cpf = null;
        if (cert && !timedOut && ("YES".equals(result) || "NO".equals(result))) {
            cpf = exportAndConvertCpf(tree.getRoot());
        }

        JSONObject response = new JSONObject();
        response.put("name", name);
        response.put("result", result);
        response.put("time", elapsed);
        response.put("timeout", timedOut);
        response.put("error", JSONObject.NULL);
        response.put("cpf", cpf != null ? cpf : JSONObject.NULL);
        response.put("proofTree", listener.toJsonArray());
        return response;
    }

    private static String exportAndConvertCpf(ProofTreeNode root) {
        Path tmpCpf2 = null;
        try {
            tmpCpf2 = Files.createTempFile("aprove_cpf2_", ".cpf");
            root.export(tmpCpf2);
            Process proc = new ProcessBuilder(CPF_CONVERTER, tmpCpf2.toString())
                .redirectError(ProcessBuilder.Redirect.INHERIT)
                .start();
            byte[] bytes = proc.getInputStream().readAllBytes();
            proc.waitFor(60, TimeUnit.SECONDS);
            return new String(bytes, "UTF-8");
        } catch (Exception e) {
            Logger.getLogger(AProVEServer.class.getName()).warning("CPF export/convert failed: " + e.getMessage());
            return null;
        } finally {
            if (tmpCpf2 != null) {
                try { Files.deleteIfExists(tmpCpf2); } catch (IOException ignored) {}
            }
        }
    }

    private static String errorResponse(String message) {
        JSONObject obj = new JSONObject();
        obj.put("result", "ERROR");
        obj.put("error", message);
        return obj.toString();
    }

    private static void redirectLoggingToStderr() {
        Logger root = Logger.getLogger("");
        // Remove handlers that write to stdout
        for (Handler h : root.getHandlers()) root.removeHandler(h);
        // Add stderr handler at WARNING level — errors remain visible but don't corrupt JSON
        Handler stderr = new StreamHandler(System.err, new SimpleFormatter());
        stderr.setLevel(Level.WARNING);
        root.addHandler(stderr);
        root.setLevel(Level.WARNING);
    }
}
