package aprove.input.Programs.haskell;

import java.io.*;
import java.util.*;
import java.util.logging.*;
import java.util.regex.*;

import aprove.input.Generated.haskell.lexer.*;
import aprove.input.Generated.haskell.node.*;
import aprove.input.Generated.haskell.parser.*;
import aprove.exit.*;
import aprove.input.Utility.*;
import aprove.runtime.*;
import aprove.verification.dpframework.HaskellProblem.*;
import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Collectors.*;
import aprove.verification.oldframework.Haskell.Expressions.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Transformations.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Annotators.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

/**
 * Translator class for the language Haskell.
 * @author Stephan Swiderski
 */
public class Translator extends aprove.verification.oldframework.Input.Translator.TranslatorSkeleton {

    public static enum PreludeVersion {

        PRELUDE_BIG {

            @Override
            public String getVersionName() {
                return "Big";
            }

        },

        PRELUDE_SMALL {

            @Override
            public String getVersionName() {
                return "Small";
            }

        };

        public Modules preludeModules = null;

        public abstract String getVersionName();

    }

    //protected static Modules preludeModules = null;
    protected static Logger log = Logger.getLogger("aprove.input.Programs.haskell.Translator");
    public boolean what = true;
    private Input input; // FIXME: We really should be stateless.

    private static List<String> searchPaths = null;

    /**
     * Gets the current paths in which imported modules will be looked for (in the order of the list)
     * @return a list of strings, or null if no search path is configured
     */
    public static List<String> getSearchPaths() {
        return Translator.searchPaths;
    }

    /**
     * Sets the paths in which modules are looked for, in the order of the list.
     * @param newSearchPath The new paths to look in for imported modules, will be used as reference, so changes to it
     *                      are reflected in here.
     */
    public static void setSearchPaths(final List<String> newSearchPath) {
        Translator.searchPaths = newSearchPath;
    }

    /**
     * Parses a colon-separated string into a list of paths in from which imported modules are loaded.
     * @param searchPathString A colon-separated string of paths, can be null which means that no search path will be
     *                         used.
     */
    public static void setSearchPaths(final String searchPathString) {
        if (searchPathString == null) {
            Translator.searchPaths = null;
            return;
        }

        final String paths[] = searchPathString.split(":");
        Translator.searchPaths = new ArrayList<String>(paths.length);
        for (final String path : paths) {
            Translator.searchPaths.add(path);
        }
    }

    @Override
    public Language getLanguage() {
        return Language.HASKELL;
    }

    public String cutLastSep(final String path) {
        final int i = path.lastIndexOf(File.separator);
        if (i < 0) {
            return "";
        }
        return path.substring(0, i);
    }

    public HaskellExp translateTerm(String term, final HaskellProgram prog) throws TranslationException {
        term = HaskellTools.parseStartTerm(term).getTerm();
        final Pair<HaskellObject, HaskellExp> pair = this.translateTermTC(term, prog);
        return pair.getValue();
    }

    public Pair<HaskellObject, HaskellExp> translateTermTC(String term, final HaskellProgram prog)
    throws TranslationException {
        HaskellExp exp = null;
        HaskellObject type = null;
        try {
            final Modules modules = prog.getModules();
            term = HaskellTools.parseStartTerm(term).getTerm();
            final Reader reader = new StringReader("\0" + term);
            final Start tree = new HaskellParser(new LayoutLexer(new PushbackReader(reader, 10240))).parse();
            final HaskellASTBuilder ab = new HaskellASTBuilder(modules, false, false);
            tree.apply(ab);
            exp = ab.getTerm();
            type = modules.checkStartTerm(exp);
        } catch (final Exception e) {
            System.err.println(e.getMessage());
            e.printStackTrace();
            throw new TranslationException(e);
        }
        return new Pair<HaskellObject, HaskellExp>(type, exp);

    }

    public void translateTermsAndAdd(final Collection<String> terms, final HaskellProgram prog)
    throws TranslationException {
        if (terms.size() == 0) {
            return;
        }
        HaskellObject type = null;
        try {
            final Modules modules = prog.getModules();
            String termStr = "";

            final List<StartTerm> startterms = new ArrayList<StartTerm>(terms.size());

            for (final String term : terms) {
                final StartTerm startterm = HaskellTools.parseStartTerm(term);
                startterms.add(startterm);
                termStr = termStr + "\0" + startterm.getTerm();
            }
            final Reader reader = new StringReader(termStr);
            final Start tree = new HaskellParser(new LayoutLexer(new PushbackReader(reader, 10240))).parse();
            final HaskellASTBuilder ab = new HaskellASTBuilder(modules, false, false);
            tree.apply(ab);

            final Iterator<StartTerm> startTerm_it = startterms.iterator();
            final Collection<Pair<HaskellObject, HaskellExp>> lazyStartterms =
                    new ArrayList<Pair<HaskellObject, HaskellExp>>();

            for (final HaskellExp exp : ab.getTerms()) {

                type = modules.checkStartTerm(exp);
                final Pair<HaskellObject, HaskellExp> typedTerm = new Pair<HaskellObject, HaskellExp>(type, exp);
                modules.addStartTerm(typedTerm);

                final StartTerm startTerm = startTerm_it.next();

                // XXX DEBUG
                if (aprove.Globals.DEBUG_MATRAF) {
                    System.err.println("SPECIFIED AS " + startTerm.getType());
                }

                if (startTerm.getType() == StartTerm.Type.LAZY_TERMINATION) {
                    lazyStartterms.add(typedTerm);
                }

            }

            if (!lazyStartterms.isEmpty()) {
                LazyReduction.applyTo(modules, null);
                LazyReduction.changeStartTerms(modules, lazyStartterms);
            }

        } catch (final Exception e) {
            System.err.println(e.getMessage());
            e.printStackTrace();
            throw new TranslationException(e);
        }
    }

    public void loadModule(final String name, final Modules modules)
    throws IOException, LexerException, ParserException {
        String path = null;

        if (Translator.searchPaths != null) {
            for (final String sp : Translator.searchPaths) {
                final File f = new File(sp + File.separator + name + ".hs");
                if (f.exists()) {
                    path = sp;
                    break;
                }
            }
        }

        // Module not found in searchPath => try directory of
        // current file or current directory
        if (path == null) {
            if (this.input == null) {
                path = new File(".").getCanonicalPath() + "/";
            } else {
                path = this.input.getPath();
            }
            path = this.cutLastSep(path);
        }

        if ("Prelude".equals(name)) {
        } else {
            Reader reader = null;
            try {
                if (Translator.searchPaths != null) {
                    for (final String sp : Translator.searchPaths) {
                        final File f = new File(sp + File.separator + name + ".hs");
                        if (f.exists()) {
                            path = sp;
                            break;
                        }
                    }

                    // Module not found in searchPath => try directory of current file or current directory
                    if (path == null) {
                        if (this.input == null) {
                            path = new File(".").getCanonicalPath() + "/";
                        } else {
                            path = this.input.getPath();
                        }
                        path = this.cutLastSep(path);
                    }
                    reader = new FileReader(path + File.separator + name + ".hs");
                } else {
                    reader = new InputStreamReader(Translator.class.getResourceAsStream(name + ".hs"));
                }
                this.loadModule(reader, modules);
            } catch (final FileNotFoundException fnfEx) {
                HaskellError.output((Token) null, "could not open module '" + name + "': " + fnfEx.getMessage());
            }
        }
    }

    public void loadModule(final Reader reader, final Modules modules)
    throws IOException, LexerException, ParserException {
        final Start tree = new HaskellParser(new LayoutLexer(new PushbackReader(reader, 10240))).parse();
        final HaskellASTBuilder ab = new HaskellASTBuilder(modules, false, false);
        tree.apply(ab);
    }

    public Pair<Modules, List<String>> loadMainModule(final Reader reader)
    throws IOException, LexerException, ParserException {
        final LayoutLexer lex = new LayoutLexer(new PushbackReader(reader, 10240));
        final Start tree = new HaskellParser(lex).parse();

        final HaskellSimplePreludeAnalyzer hspa = new HaskellSimplePreludeAnalyzer();
        tree.apply(hspa);

        // XXX DEBUG
        if (aprove.Globals.DEBUG_MATRAF) {
            System.err.println("SIMPLE PRELUDE COMPATIBLE: " + hspa.isSimplePreludeCompatible());
        }

        final Modules modules = Translator.readPrelude(PreludeVersion.PRELUDE_BIG);

        final HaskellASTBuilder ab = new HaskellASTBuilder(modules, true, false);
        tree.apply(ab);

        final List<String> startterms = new ArrayList<String>(lex.startterms.size());

        Startterm_Search: for (final Pair<Token, String> starttermTokText : lex.startterms) {
            final String startterm = starttermTokText.y;

            StartTerm.Type starttermType = null;
            for (final String part : startterm.split(" ")) {
                if (part.matches("\\s*")) {
                    continue;
                }
                starttermType = StartTerm.Type.getTypeOf(part);
                if (starttermType == null) {
                    // allow for GHC pragmas, etc.
                    continue Startterm_Search;

                    // HaskellError.output(starttermTokText.x, "no valid keyword: "+part);
                }
                break;
            }

            /*
             * int pos = startterm.indexOf(HTERMINATION_KEYWORD+" "); if (pos <
             * 0) { HaskellError.output(starttermTokText.x,
             * "no "+HTERMINATION_KEYWORD+" found in embedded start term"); }
             * startterm =
             * startterm.substring(pos+HTERMINATION_KEYWORD.length()+1);
            */

            assert (starttermType != null);
            final int pos = startterm.indexOf(starttermType.getKeyword() + " ");
            final StringBuilder sb = new StringBuilder();
            sb.append('<');
            sb.append(starttermType.getKeyword());
            sb.append('>');
            sb.append(startterm.substring(pos + starttermType.getKeyword().length()));

            startterms.add(sb.toString());
        }
        return new Pair<Modules, List<String>>(modules, startterms);
    }

    public static void loadPrelude(final PreludeVersion version, final Modules modules)
    throws IOException, LexerException, ParserException {
        final Reader reader = Translator.getPreludeReader(version);
        final Start tree = new HaskellParser(new LayoutLexer(new PushbackReader(reader, 10240))).parse();
        modules.setPrelude(new Prelude(null, version == PreludeVersion.PRELUDE_SMALL));
        final HaskellASTBuilder ab = new HaskellASTBuilder(modules, false, true);
        tree.apply(ab);
    }

    @Override
    public void translate(final Reader reader) {
        throw new RuntimeException("DON'T CALL ME");
    }

    @Override
    public void translate(final Input input) throws TranslationException {
        this.input = input;
        final Reader reader = input.getContent();

        this.setState(null); // new HaskellProgram();
        try {
            //Modules mods = readPrelude();
            final Pair<Modules, List<String>> modulesAndstartterms = this.loadMainModule(reader);
            final Modules mods = modulesAndstartterms.x;
            final List<String> startterms = modulesAndstartterms.y;

            while (mods.needMoreModules()) {
                this.loadModule(mods.getNextNeededModule(), mods);
            }

            final PositivityChecker positivityChecker = new PositivityChecker();
            positivityChecker.check(mods);

            this.setState(mods.buildHaskellProgram());
            //JTreeDialog.create("Modules",new StructureTreeModel(new ReflectTreeEntry("","Modules",mods))).show();

            final HaskellProgram hp = (HaskellProgram) this.getState();
            String s = "", sep = "";
            for (final String startterm : startterms) {
                final Pair<HaskellObject, HaskellExp> typedTerm = this.translateTermTC(startterm, hp);
                final QuantorExp quanTerm = (QuantorExp) typedTerm.y;
                final Set<Var> freeVars = new HashSet<Var>();
                final FreeLocalVarCollector flvc = new FreeLocalVarCollector(freeVars);
                quanTerm.getResult().visit(flvc);

                if (!freeVars.isEmpty()) {
                    final StringBuilder sb = new StringBuilder();
                    String sep2 = "";
                    for (final Var v : freeVars) {
                        sb.append(sep2);
                        sep2 = ", ";
                        sb.append(v.getSymbol().getName(false));
                    }
                    HaskellError.output(
                        typedTerm.x,
                        "Embedded start terms must not contain free variables, found: " + sb.toString()
                    );
                }

                s += sep + startterm;
                sep = Character.toString(HaskellAnnotator.STARTTERM_SEPARATOR);
            }
            if (s.length() > 0) {
                input.setProtoAnnotation(s);
            }

        } catch (final ParserException e) {
            this.handlePLException(e);
            this.setState(null);
        }catch (final StrictPositivityException e) {
            final ParseError pe = new ParseError(ParseError.ERROR);
            pe.setMessage(e.getMessage());
            this.getErrors().add(pe);
            this.setState(null);
//            throw e;
        } catch (final LexerException e) {
            this.handlePLException(e);
            this.setState(null);
        } catch (final IOException e) {
            throw new TranslationException(e);
        } catch (final HaskellError e) {
            final ParseError pe = new ParseError(ParseError.ERROR);
            final Token t = e.getToken();
            if (t != null) {
                pe.setToken(t.toString().trim());
                pe.setPosition(t.getLine(), t.getPos());
            } else {
                pe.setToken("");
                pe.setPosition(1, 1);
            }
            System.err.println("HaskellError:::::::::::::::::::::::::" + e.getMessage());
            pe.setMessage(e.getMessage());
            this.getErrors().add(pe);
            this.setState(null);
        }
    }

    private void handlePLException(final Exception e) {
        final ParseError pe = new ParseError(ParseError.ERROR);
        if (e instanceof ParserException) {
            final Token t = ((ParserException) e).getToken();
            pe.setToken(t.toString().trim());
            pe.setPosition(t.getLine(), t.getPos());
        } else if (e instanceof LexerException) {
            try {
                final Matcher m = Pattern.compile(".*\\0133([0-9]+),([0-9]+)\\0135\\s.*").matcher(e.getMessage());
                m.matches();
                pe.setPosition(Integer.parseInt(m.group(1)), Integer.parseInt(m.group(2)));
            } catch (final Exception e1) {
                System.err.println(e1.getMessage());
            }
        }
        pe.setMessage(e.getMessage().replaceFirst("\\0133[0-9]+,[0-9]+\\0135\\s", ""));
        this.getErrors().add(pe);
    }

    public static void main(final String[] argv) {
        try {
            doMain(argv);
        } catch (KillAproveException e) {
            e.runSystemExit();
        }
    }

    private static void doMain(final String[] argv) throws KillAproveException {
        if (argv[0].equals("prelude")) {
            if (argv.length < 3) {
                System.err.print("ERROR: must be called with arguments prelude [target file] (");
                boolean first = true;
                for (final PreludeVersion ver : PreludeVersion.values()) {
                    if (!first) {
                        System.err.print(" | ");
                    } else {
                        first = false;
                    }
                    System.err.print(ver.toString());
                }
                System.err.println(")");
                throw new KillAproveException(1);
            }
            try {
                Translator.generatePreludeFile(PreludeVersion.valueOf(argv[2]), argv[1]);
            } catch (final Exception e) {
                System.err.println(e.getMessage());
                e.printStackTrace();
                throw new KillAproveException(1);
            }
            System.err.println("Prelude " + PreludeVersion.valueOf(argv[2]) + " built.");
            return;
        } else if (argv[0].equals("serialize")) {
            if (argv.length < 3) {
                System.err.println("invocation: serialize [module to load] [save location]");
                throw new KillAproveException(1);
            }
            final Modules mods = new Modules();
            try {
                Translator.loadPrelude(PreludeVersion.PRELUDE_BIG, mods);
            } catch (final Exception e) {
                throw new RuntimeException(e);
            }
            // mods.buildPrelude();
            final Translator trans = new Translator();
            try {
                trans.loadModule(argv[1], mods);
                while (mods.needMoreModules()) {
                    trans.loadModule(mods.getNextNeededModule(), mods);
                }
                mods.buildPrelude();
                for (final Module m : mods.getModules()) {
                    m.setAlreadyLoaded(true);
                }
                Translator.savePrelude(new File(argv[2]), mods);
            } catch (final Exception e) {
                System.err.println("could not load module " + argv[1]);
                throw new RuntimeException(e);
            }
            System.err.println("Serialization done.");
        }

        final Translator ts = new Translator();
        try {
            ts.input = new FileInput(new File(argv[0]));
            ts.translate(new File(argv[0]));
        } catch (final Exception e) {
            System.err.println(e.getMessage());
            e.printStackTrace();
        }
        /*
         * System.err.println(argv[1]); HaskellProgram prog = ((HaskellProgram)
         * ts.getState()); try { ts.translateTerm(argv[1],prog); } catch
         * (Exception e) { System.err.println(e.getMessage());
         * e.printStackTrace(); }
        */
        try {
            System.err.println("\n\n start output");
            {
                final String html = ((HaskellProgram) ts.getState()).toPLAIN();
                final FileWriter fw = new FileWriter(argv[1]);
                fw.write(html);
                fw.flush();
                fw.close();
            }
            {
                final String html = ((HaskellProgram) ts.getState()).toXML();
                final FileWriter fw = new FileWriter(argv[2]);
                fw.write(html);
                fw.flush();
                fw.close();
            }
            System.err.println("\n\nAll Done, no exception");
        } catch (final Exception e) {
            System.err.println(e.getMessage());
            e.printStackTrace();
        }
    }

    public static Reader getPreludeReader(final PreludeVersion version) {
        return new InputStreamReader(
            Translator.class.getResourceAsStream("Prelude" + version.getVersionName() + ".hs")
        );
    }

    public static void generatePreludeFile(final PreludeVersion version, final String fileName)
    throws IOException, LexerException, ParserException {
        final Modules mods = new Modules();
        Translator.loadPrelude(version, mods);
        mods.buildPrelude();
        Translator.savePrelude(new File(fileName), mods);
    }

    public static void savePrelude(final File file, final Modules modules) {
        try {
            final ObjectOutputStream out = new ObjectOutputStream(new FileOutputStream(file));
            out.writeObject(modules);
            out.close();
        } catch (final IOException e) {
            file.delete();
            throw new RuntimeException("internal error: object could not be serialized: " + e.getMessage()); //should not happen
        }
    }

    // synchronized, because it shall be able to call it upon startup, so that the serialized Prelude is already loaded
    public static synchronized Modules readPrelude(final PreludeVersion version) {
        final aprove.verification.oldframework.Utility.Timer timer = new aprove.verification.oldframework.Utility.Timer();
        timer.start();
        if (version.preludeModules == null) {
            Translator.log.log(Level.INFO, "Loading Prelude " + version.toString() + " the first time\n");
            Object newObj = null;

            String filename = Options.serializationModulesSource;
            InputStream ins;
            if (filename == null) {
                filename = "Prelude" + version.getVersionName() + "Ser.hs";
                ins = Translator.class.getResourceAsStream(filename);
            } else {
                try {
                    ins = new FileInputStream(filename);
                } catch (final FileNotFoundException e) {
                    throw new RuntimeException(e);
                }
            }

            // XXX DEBUG
            if (aprove.Globals.DEBUG_MATRAF) {
                System.err.println("Trying to read from file " + filename);
            }

            try {
                final ObjectInputStream in = new ObjectInputStream(ins);
                newObj = in.readObject();
                in.close();
            } catch (final Exception e) {
                e.printStackTrace();
                throw new RuntimeException("internal error: object could not be deserialized: " + e.getMessage()); //should not happen
            }
            version.preludeModules = (Modules) newObj;
            Translator.log.log(Level.INFO, "Prelude loaded. \n");
        }
        final Modules nmods = Modules.createModules(version.preludeModules);
        timer.stop();
        final double timerTime = timer.getDuration() / 1000;
        Translator.log.log(Level.INFO, "Loading Prelude took " + timerTime + " s\n");

        // XXX DEBUG
        if (aprove.Globals.DEBUG_MATRAF) {
            System.err.println("Loading Prelude took " + timerTime + " s");
        }

        //HaskellSym.showee(new Pair(preludeModules,nmods));
        return nmods;
        //        return preludeModules;
    }

}
