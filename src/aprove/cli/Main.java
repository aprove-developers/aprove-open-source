package aprove.cli;

import gnu.getopt.*;

import java.io.*;
import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.Globals.AproveVersion;
import aprove.exit.*;
import aprove.input.*;
import aprove.input.Programs.ariTrs.*;
import aprove.logging.*;
import aprove.logging.config.*;
import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.strategies.Parameters.*;
import aprove.strategies.Util.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.CPF.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class Main {

    private final static String HTML_FOOTER = "</BODY></HTML>";

    private String fileName;
    private AProVE AProVE;
    private String witnessFile;

    public static void main(final String argv[]) {
        try {
            doMain(argv);
        } catch (KillAproveException e) {
            e.runSystemExit();
        }
    }

    public static TruthValue doMain(final String[] argv) throws KillAproveException {
        return new Main().run(argv);
    }

    public TruthValue run(String argv[]) throws KillAproveException {
        final aprove.verification.oldframework.Utility.Timer timer = new aprove.verification.oldframework.Utility.Timer();

        aprove.Main.UI_MODE = aprove.Main.UI.CLI;

        final Pair<CLIOpts, Getopt> optResult = Main.parseCommandLineOptions(argv);
        final CLIOpts options = optResult.x;
        final Getopt g = optResult.y;

        CliOverrides.set(options.goalOverride, options.strategyOverride, options.startTermOverride);
        this.fileName = "<no file>";
        try {
            Main.initLogging(options.level);

            if (options.bitwidth.equals("32") || options.bitwidth.equals("64")) {
                Globals.bitwidth = options.bitwidth;
            } else {
                System.err.println("Invalid bit-width. Use --bit-width with 32 or 64.");
            }

            if (options.certifier != null) {
                Main.initCertifier(options);
            }

            final Input input = this.getInput(argv, options, g);
            final CPFOnlineChecker checker =
                CPFOnlineChecker.createCPFOnlineChecker(Options.onlineCertification, this.fileName);
            BasicObligationNode.setCPFOnlineChecker(checker);

            if (options.handlingMode == null) {
                this.AProVE = new AProVE(input);
            } else {
                this.AProVE = new AProVE(input, options.handlingMode);
            }

            if (options.strategyName != null) {
                this.AProVE.setStrategy(Main.loadStrategy(options.strategyName));
            } else if (options.bitvectors) {
                this.AProVE.setStrategy(EasyInput.loadStrategyModule("aprove.Auto.current-bv"));
            }
            if (options.timeout > 0) {
                this.AProVE.setTimeout(1000L * options.timeout);
            }

            // Workaround for now: Typecheck even predefined strategies,
            // until we are certain they are fully error-free.
            if (Options.performEagerChecking && options.strategyName == null) {
                this.AProVE.getEffectiveStrategy().eagerCheck();
            }

            if (options.witnessFile != null) {
                this.witnessFile = options.witnessFile;
                Globals.generateGraphmlWitness = true;
            }

            timer.start();
            final boolean killed = this.AProVE.run();
            timer.stop();

            final ObligationNode root = this.AProVE.getRoot();

            // ugly quickfix: this hack should NOT be necessary here!
            // TODO grok (i.e., really completely understand) the truth value
            // management of the proof tree
            if (!root.isTruthValueKnown()) {
                root.recursiveRepropagateTruthValues();
                if (root.isTruthValueKnown()) {
                    final Logger log = Logger.getLogger("aprove.CommandLineInterface.Main");
                    if (log.isLoggable(Level.WARNING)) {
                        log.warning("Truth value repropagation in proof tree changed value to "
                            + root.getTruthValue().toWstString());
                    }
                }
            }

            if (options.mode == Mode.WST || options.mode == Mode.BENCHMARK) {
                if (killed) {
                    if (!root.getTruthValue().isCompletelyUnknown()) {
                        this.printResult(root.getTruthValue(), options.mode);
                    } else {
                        System.out.println("KILLED");
                      	System.out.println("\nFound an example we currently can't prove?\n"
                    			+ "-> Consider contributing it to the benchmark set: https://mysolvertimesout.org/\n");
                    }
                } else {
                    this.printResult(root.getTruthValue(), options.mode);
                }
            }
            if (this.witnessFile != null) {
                if ("NO".equals(root.getTruthValue().toWstString())) {
                    root.printGraphmlWitness(this.witnessFile);
                }
            }
            if (options.printNontermWitness) {
                if ("NO".equals(root.getTruthValue().toWstString())) {
                    final TRSTerm t = root.getNonterminatingTerm();
                    if (t == null) {
                        System.out.println("(Non-terminating start term could not be retrieved.)");
                    } else {
                        final String tString = t.toString();
                        System.out.println(tString);
                    }
                }
            }
            if (options.debug) {
                System.out.format("%.2f\n", timer.getDuration() / 1000);
            }
            options.export.export(root, this.fileName);
            if (checker != null) {
                checker.printStatistic();
            }
            return root.getTruthValue();
        } catch (KillAproveException e) {
            throw e;
        } catch (final Exception e) {
            if (options.debug || Globals.aproveVersion == AproveVersion.DEVELOPER_VERSION) {
                e.printStackTrace();
                e.printStackTrace(System.out);
            }
            if (options.mode == Mode.WST || options.mode == Mode.BENCHMARK) {
                System.out.println("ERROR");
            } else if (options.mode == Mode.APROVE) {
                timer.stop();
                System.out.printf("E %.2f %s%n", timer.getDuration() / 1000, this.fileName);
            } else if (options.mode == Mode.CGI) {
                System.out.println("<P><H2>An error occurred!</H2></P>" + Main.HTML_FOOTER);
            }
            return null;
        } finally {
            CliOverrides.clear();
        }
    }

    private void printResult(TruthValue res, Mode mode) {
        if (mode == Mode.WST) {
            System.out.println(res.toWstString());
            if (res.fallbackToYNM().equals(YNM.MAYBE)) {
            	System.out.println("\nFound an example we currently can't prove?\n"
            			+ "-> Consider contributing it to the benchmark set: https://mysolvertimesout.org/\n");
            }
        } else {
            assert mode == Mode.BENCHMARK;
            System.out.println(res.toBenchmarkResult());
        }
    }

    public ObligationNode getRoot() {
        return this.AProVE.getRoot();
    }

    static boolean IS_MODULE(final String strategyName) {
        //System.out.println("Analyzing "+strategyName);
        return (strategyName.startsWith("aprove."));
    }

    private Input getInput(final String[] argv, final CLIOpts options, final Getopt g) throws KillAproveException {
        Input result;
        String forcedExt = null;
        if (options.ext != null && !options.ext.equals("cgi")) {
            forcedExt = options.ext;
        }
        if (g.getOptind() >= argv.length) {
            result = new ConsoleInput(forcedExt, options.query);
            this.fileName = result.getName();
        } else {
            this.fileName = argv[g.getOptind()];
            result = new FileInput(new File(this.fileName), forcedExt, options.query);
            if (result.getExtension().equals("list")) {
                System.err.println("Support for .list targets was removed to simplify Main.");
                System.err.println("Please use Batch instead if you need multiple targets.");
                throw new KillAproveException(1);
            }
        }
        if (!result.isAvailable()) {
            final String errMsg = "Cannot read from " + result.getName();
            if (Globals.aproveVersion == Globals.AproveVersion.DEVELOPER_VERSION) {
                System.err.println(errMsg);
            }
            throw new IllegalArgumentException(errMsg);
        }
        return result;
    }

    private static void initCertifier(final CLIOpts options) {
        Options.certifier = options.certifier;
        if (Options.certifier.isRainbow() && Options.certifier.isA3pat()) {
            System.err.println("Warning: Flags rainbow & a3pat are both set, results may be compromised");
        }
        if (options.strategyName == null) {
            options.strategyName = options.certifier.getDefaultStrategyName();
            if (Globals.useAssertions) {
                assert Main.IS_MODULE(options.strategyName);
            }
        }
    }

    private static void initLogging(final String level) {
        final Level logLevel;
        if (level != null) {
            logLevel = Level.parse(level);
        } else {
            if (Globals.aproveVersion == Globals.AproveVersion.RELEASE_VERSION || Options.isWebInterfaceMode) {
                logLevel = Level.SEVERE;
            } else {
                logLevel = Level.WARNING;
            }
        }
        LogConfig.init("cli");
        final Logger rootLogger = Logger.getLogger("");
        rootLogger.setLevel(logLevel);
    }

    private static StrategyProgram loadStrategy(final String strategyName) throws KillAproveException {
        StrategyProgram result;
        if (Main.IS_MODULE(strategyName)) {
            result = EasyInput.loadStrategyModule(strategyName);
        } else {
            result = EasyInput.loadStrategy(strategyName);
        }
        if (Options.performEagerChecking) {
            result.eagerCheck();
        }
        return result;
    }

    private static Pair<CLIOpts, Getopt> parseCommandLineOptions(final String[] argv) throws KillAproveException {
        LongOpt[] longopts = new LongOpt[4];
        longopts[0] = new LongOpt("bit-width", LongOpt.REQUIRED_ARGUMENT, null, 'B');
        longopts[1] = new LongOpt("goal", LongOpt.REQUIRED_ARGUMENT, null, 'G');
        longopts[2] = new LongOpt("rewrite-strategy", LongOpt.REQUIRED_ARGUMENT, null, 'R');
        longopts[3] = new LongOpt("startterm", LongOpt.REQUIRED_ARGUMENT, null, 'S');
        final Getopt g = new Getopt("AProVE CLI", argv, "a:bc:C:Z:de:f:h:i:l:m:no:p:q:rs:t:u:v:w:xzB:FP:M::O:T:W:G:R:S:", longopts);
        int c;
        final CLIOpts options = new CLIOpts();
        while ((c = g.getopt()) != -1) {
            switch (c) {

            case 'a':
                final String stringMode = g.getOptarg();
                if (stringMode.equals("termination")) {
                    options.handlingMode = HandlingMode.Termination;
                } else if (stringMode.equals("theoremprover")) {
                    options.handlingMode = HandlingMode.TheoremProver;
                } else if (stringMode.equals("complexity")) {
                    options.handlingMode = HandlingMode.RuntimeComplexity;
                } else {
                    System.err.println("Illegal handling mode '" + stringMode + "' given!");
                }
                break;
            case 'b':
                options.bitvectors = true;
                break;
            // graph eXport ('g' is taken in Release 1.2, therefore avoiding it)
            case 'x':
                // deprecated, no jdotty
                //Options.exportGraphs = true;
                break;

            // Haskell modules serialization
            case 'h':
                Options.serializationModulesSource = g.getOptarg();
                break;

            case 'F':
                Options.performEagerChecking = false;
                break;

            // Haskell modules search Path
            case 'P':
                aprove.input.Programs.haskell.Translator.setSearchPaths(g.getOptarg());
                break;

            case 'v':
                options.level = g.getOptarg();
                if (options.level == null) {
                    options.level = "INFO";
                }
                break;
            case 'p':
                final String proofType = g.getOptarg();
                if (proofType.equals("html")) {
                    options.export = ProofExport.HTML;
                } else if (proofType.equals("fhtml")) {
                    options.export = ProofExport.HTML;
                } else if (proofType.equals("oldhtml")) {
                    options.export = ProofExport.OLDHTML;
                } else if (proofType.equals("tex")) {
                    options.export = ProofExport.LATEX;
                } else if (proofType.equals("oldplain")) {
                    options.export = ProofExport.OLDPLAIN;
                } else if (proofType.equals("plain")) {
                    options.export = ProofExport.PLAIN;
                } else if (proofType.equals("xml")) {
                    options.export = ProofExport.XML;
                } else if (proofType.equals("cpf")) {
                    options.export = ProofExport.CPF;
                } else if (proofType.equals("cime")) {
                    options.export = ProofExport.DIO_CIME;
                }
                break;
            case 'm':
                final String m = g.getOptarg();
                if (m.equals("wst")) {
                    options.mode = Mode.WST;
                } else if (m.equals("aprove")) {
                    options.mode = Mode.APROVE;
                } else if (m.equals("cgi")) {
                    options.mode = Mode.CGI;
                    if (options.export == ProofExport.NONE) {
                        options.export = ProofExport.HTML;
                    }
                    Options.isWebInterfaceMode = true;
                } else if (m.equals("quiet")) {
                    options.mode = Mode.QUIET;
                } else if (m.equals("benchmark")) {
                    options.mode = Mode.BENCHMARK;
                }
                break;
            case 'n': // for NO on TRS input, give a witness term after the WST output
                options.printNontermWitness = true;
                break;
            case 'd':
                options.debug = true;
                break;
            case 's':
                options.strategyName = g.getOptarg();
                break;
            case 'e':
                options.ext = g.getOptarg();
                break;
            case 'f':
                throw new UnsupportedOperationException("-f was broken. Implement me again.");
                //break;
            case 't':
                final String timeout = g.getOptarg();
                try {
                    options.timeout = Integer.parseInt(timeout);
                } catch (final NumberFormatException e) {
                    System.err.println("Failed to parse timeout '" + timeout + "', ignoring.");
                }
                break;
            case 'q':
                options.query = g.getOptarg();
                break;
            case 'l':
                Options.lemmaDatabaseFileName = g.getOptarg();
                break;
            case 'c':
                Options.csvName = g.getOptarg();
                if (Globals.useAssertions) {
                    if (Certifier.parseName(Options.csvName) != null) {
                        throw new UnsupportedOperationException(
                            "Arguments to '-c' like "
                            + Options.csvName
                            + " that could be interpreted as a certifier name are not supported (it's a csv file for "
                            + "logging data).");
                    }
                }
                break;
            case 'i':
                final String exampleId = g.getOptarg();
                try {
                    Options.exampleId = Integer.parseInt(exampleId);
                } catch (final NumberFormatException e) {
                    System.err.println("Failed to parse example ID '" + exampleId + "', ignoring.");
                }
                break;
            case 'B':
                String arg = g.getOptarg();
                options.bitwidth = arg;
                break;
            case 'C':
                options.certifier = Certifier.parseName(g.getOptarg());
                break;
            case 'Z':
                Options.onlineCertification = g.getOptarg();
                break;
            case 'M':
                AproveOutput.setMultiOutputFromParam(g.getOptarg());
                break;
            case 'O':
                final String varEqVal = g.getOptarg();
                final int eqIndex = varEqVal.indexOf('=');
                if (eqIndex < 0) {
                    Options.set(varEqVal, Optional.empty());
                } else {
                    Options.set(varEqVal.substring(0, eqIndex), Optional.of(varEqVal.substring(eqIndex + 1)));
                }
                break;
            case 'T':
                arg = g.getOptarg().toLowerCase();
                Options.defaultThreadingHasPriority = arg.equals("high");
                break;
            case 'w':
                arg = g.getOptarg();
                int workers;
                try {
                    workers = Integer.parseInt(arg);
                } catch (final NumberFormatException e) {
                    workers = -1;
                }
                if (workers > 0) {
                    PrioritizableThreadPool.INSTANCE.setTargetWorkers(workers);
                } else {
                    // Use standard value on error
                    System.err.println("Invalid worker count '" + arg + "'! Using the default.");
                }
                break;
            case 'W':
                arg = g.getOptarg();
                options.witnessFile = arg;
                break;

            case 'G':
                options.goalOverride = g.getOptarg().toLowerCase();
                break;
            case 'R':
                options.strategyOverride = g.getOptarg().toLowerCase();
                break;
            case 'S':
                options.startTermOverride = g.getOptarg().toLowerCase();
                break;

            /* Parameters without effect */
            case 'o':
            case 'r':
            case 'z':
                System.err.println("Option " + Character.toString((char) c) + " is not supported anymore. Ignoring.");
                break;
            }
        }

        return new Pair<>(options, g);
    }

    /**
     * Parsed command line options
     */
    private static class CLIOpts {
        boolean bitvectors = false;
        String bitwidth = "64";
        Certifier certifier = null;
        boolean debug = false;
        ProofExport export = ProofExport.NONE;
        String ext = null;
        HandlingMode handlingMode = null;
        String level = null;
        Mode mode = Mode.APROVE;
        boolean printNontermWitness = false; // currently only for TRSs
        String query = null;
        String strategyName = null;
        int timeout = 0;
        String witnessFile;
        // .ari file declaration overrides
        String goalOverride = null;       // --goal <ast|sast|termination|complexity|confluence|infeasibility|past>
        String strategyOverride = null;   // --rewrite-strategy <innermost|outermost|full>
        String startTermOverride = null;  // --startterm <all|basic>
    }

    private static enum Mode {
        APROVE,
        CGI,
        QUIET,
        WST,
        // like WST, but allows for more detailed lower bounds:
        // while the wst format (of 2015) just permits NON_POLY,
        // we want to have 2^n, 3^n, ..., EXP, INF for our benchmarks
        BENCHMARK
    }
}
