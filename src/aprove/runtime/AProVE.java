package aprove.runtime;

import java.util.*;
import java.util.logging.*;

import aprove.*;
import aprove.input.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.strategies.Parameters.*;
import aprove.verification.dpframework.JBCProblem.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Input.Annotators.*;
import aprove.verification.oldframework.Input.TypeAnalyzers.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.theoremprover.ObligationFactories.*;

/**
 * This class serves as a central implementation of parsing and solving of input
 * problems.
 *
 */
public class AProVE implements ProveRunner {

    private static final Logger log = Logger.getLogger("aprove.runtime.AProVE");

    static boolean waitForHandle(final StrategyExecutionHandle handle, final long timeoutOrNegative) {
        boolean killed;

        try {
            if (timeoutOrNegative <= 0) {
                handle.waitForFinish();
                killed = false;
            } else {
                killed = !handle.waitForFinish(timeoutOrNegative);
            }
        } catch (final InterruptedException e) {
            System.err.println("AProVE interrupted!");
            killed = true;
        }
        if (killed) {
            handle.stop("Timeout reached.");
        }

        return killed;
    }

    private StrategyExecutionHandle handle;
    private final Input input;
    private final Map<Metadata, Object> metadata;
    private List<BasicObligationNode> positions;
    private StrategyProgram presetStrategy = null;
    private ObligationNode root;
    private long timeout = 0;
    private TypedInput typedInput;

    public AProVE(final Input input) throws SourceException {
        this.input = input;
        Globals.programFile = input.getPath();
        this.parse(null);
        this.metadata = this.buildMetadata();
    }

    public AProVE(final Input input, final HandlingMode handlingMode) throws SourceException {
        this.input = input;
        this.parse(handlingMode);
        this.metadata = this.buildMetadata();
    }

    public AProVE(final BasicObligation obligation, final Language language, final String name) {
        this.input = null;
        this.typedInput = new TypedInput(ModedType.createModedInput(language), obligation, null);
        final BasicObligationNode node = new BasicObligationNode(obligation);
        this.root = node;
        this.positions = Collections.singletonList(node);
        this.metadata = buildDirectMetadata(name);
        Main.firstObligation = false;
    }

    private Map<Metadata, Object> buildDirectMetadata(final String name) {
        final Map<Metadata, Object> result = new EnumMap<>(Metadata.class);
        result.put(Metadata.PROBLEM_PATH_NAME, name);
        return result;
    }

    public StrategyProgram getEffectiveStrategy() {
        if (this.presetStrategy != null) {
            return this.presetStrategy;
        } else {
            return AutoManager.getStrategyProgramForTypedInput(this.typedInput);
        }
    }

    /* (non-Javadoc)
     * @see aprove.runtime.ProveRunner#getResult()
     */
    @Override
    public ExecutableStrategy getResult() {
        return this.handle.getResult();
    }

    public ObligationNode getRoot() {
        return this.root;
    }
    
    public TypedInput getTypedInput() {
        return this.typedInput;
    }

    /* (non-Javadoc)
     * @see aprove.runtime.ProveRunner#run()
     */
    @Override
    public boolean run() {
        final StrategyProgram strategy = this.getEffectiveStrategy();
        this.handle = Machine.theMachine.start(null, strategy, this.positions, this.metadata);

        return AProVE.waitForHandle(this.handle, this.timeout);
    }

    public void setMetadata(final Metadata key, final Object value) {
        this.metadata.put(key, value);
    }

    public void setStrategy(final StrategyProgram strategyProgram) {
        this.presetStrategy = strategyProgram;
    }

    public void setTimeout(final long millis) {
        this.timeout = millis;
    }

    public void stop() {
        this.handle.stop("GUI stop button pressed");
    }

    Map<Metadata, Object> buildMetadata() {
        final Map<Metadata, Object> result = new EnumMap<Metadata, Object>(Metadata.class);

        final String extension = this.input.getExtension();
        if (extension.equals("srs") || extension.equals("ses")) {
            result.put(Metadata.IS_SRS, Boolean.TRUE);
        }

        result.put(Metadata.PROBLEM_PATH_NAME, this.input.getName());

        // Temporary hack until non-COMPLETE support is properly implemented
        // (Java programs will start out with a SOUND transformation, see JBCToTerminationGraphProcessor)
        if (this.positions.get(0).getBasicObligation() instanceof JBCProblem) {
            result.put(Metadata.AVOID_NONTERM, Boolean.TRUE);
        }

        return result;
    }

    private void forceHandlingMode(final HandlingMode forcedHandling) {
        if (!this.typedInput.getModedType().setMode(forcedHandling)) {
            AProVE.log.info("Could not set handling mode "
                + forcedHandling
                + " for "
                + this.typedInput
                + ". Continuing with "
                + "handling mode"
                + this.typedInput.getHandlingMode()
                + ".");
        }
    }

    private void parse(final HandlingMode forcedHandling) throws SourceException {
        final ExtensionTypeAnalyzer eta = new ExtensionTypeAnalyzer();
        this.typedInput = eta.analyze(this.input);
        if (forcedHandling != null) {
            this.forceHandlingMode(forcedHandling);
        }
        final PublicAnnotator annotator = new DefaultAnnotator();
        final AnnotatedInput annotate = annotator.annotate(this.typedInput);
        final ObligationFactory of = new MetaObligationFactory();
        final Pair<ObligationNode, List<BasicObligationNode>> rootAndPositions = of.getRootAndPositions(annotate);
        Main.firstObligation = false;
        this.root = rootAndPositions.x;
        this.positions = rootAndPositions.y;
    }

}
