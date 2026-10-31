package aprove.verification.oldframework.Input.TypeAnalyzers;

import java.io.*;
import java.util.*;

import aprove.input.Programs.haskell.StrictPositivityException;
import aprove.input.Utility.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Rewriting.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.theoremprover.TheoremProver.*;

/**
 * Determine type of program by extension.
 *
 * @author nowonder
 * @version $Id: ExtensionTypeAnalyzer.java,v 1.11 2006/06/28 18:21:38 dickmeis
 *          Exp $
 */

public class ExtensionTypeAnalyzer implements TypeAnalyzer {

    private static final Properties props = ExtensionTypeAnalyzer.loadProperties();
    private final String forcedExt;

    public ExtensionTypeAnalyzer() {
        this.forcedExt = null;
    }

    /**
     * Construct an instance that interprets all inputs to have a given extension.
     *
     * @deprecated Prefer constructing your Input so it reports the appropriate extension.
     */
    @Deprecated
    public ExtensionTypeAnalyzer(final String forcedExt) {
        this.forcedExt = forcedExt;
    }

    @Override
    public TypedInput analyze(final Input input) throws ParserErrorsSourceException {
        final Translator trans = this.getTranslator(input);
        if (input.getProtoAnnotation() != null) {
            trans.setProtoAnnotation(input.getProtoAnnotation());
        }
        try {
            trans.translate(input);
        } catch (final Exception e) {
            e.printStackTrace();
        }
        final Object prog = trans.getState();
        if (!trans.getErrors().isEmpty()
                && trans.getErrors().getMaxLevel() >= aprove.input.Utility.ParseError.ERROR) {
            // System.out.println(trans.getErrors());
            final ParseErrors errors = trans.getErrors();
            final ParserErrorsSourceException excp = new ParserErrorsSourceException(
                    errors, input);
            throw excp;
        }
        ModedType mType = ModedType.createModedInput(trans.getLanguage());
        mType = ExtensionTypeAnalyzer.overrideMode(mType, prog);
        return new TypedInput(mType, prog, input);
    }

    private static ModedType overrideMode(ModedType mType, Object prog) {
        Language lang = mType.getLanguage();
        if (lang.equals(Language.TES)
                && ((Program) prog).isMaxUnary()) {
            mType = ModedType.createModedInput(Language.SES);
        } else if (lang.equals(Language.TRS)
                && ((Program) prog).isMaxUnary()) {
            mType = ModedType.createModedInput(Language.SRS);
        } else if (lang.equals(Language.FP)
                && !((ProgramContainingFormulas) prog).getFormulas().isEmpty()) {
            // if an FP program contains formulas
            // we assume that they have to be proven by the theorem prover
            mType.setMode(HandlingMode.TheoremProver);
        }
        return mType;
    }

    private Translator getTranslator(final Input input) {
        if (this.forcedExt == null) {
            return ExtensionTypeAnalyzer.transForExt(input.getExtension());
        } else {
            return ExtensionTypeAnalyzer.transForExt(this.forcedExt);
        }
    }

    public static Translator transForExt(String ext) {
        String classname = ExtensionTypeAnalyzer.props.getProperty(ext);
        if (classname == null) {
            classname = ExtensionTypeAnalyzer.props.getProperty("DEFAULT");
            if (classname == null) {
                throw new RuntimeException("Where is my default Translator?");
            }
        }
        try {
            return (Translator)Class.forName(classname).newInstance();
        } catch (final Exception e) {
            throw new RuntimeException("Where is my " + classname + "?");
        }
    }

    private static Properties loadProperties() {
        final Properties defaultprops = new Properties();
        try {
            PropertyLoader.fromResource(defaultprops, Input.class, "extension.properties");
        } catch (final IOException e) {
            System.err.println(e.getMessage());
            throw new RuntimeException("Where are my default props? D'oh!");
        }
        Properties result = new Properties(defaultprops);
        try {
            PropertyLoader.fromFile(result, System.getProperty("user.home")
                    + "/.aprove/extension.properties");
        } catch (final IOException e) {
            // Ignore, use global properties only then.
        }
        return result;
    }

}
