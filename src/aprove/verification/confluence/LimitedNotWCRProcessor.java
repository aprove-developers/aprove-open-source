package aprove.verification.confluence;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.ParamsViaArgumentObject;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.confluence.Utility.*;
import aprove.verification.dpframework.*;


public class LimitedNotWCRProcessor implements Processor {
    private final Arguments args;

    @ParamsViaArgumentObject
    public LimitedNotWCRProcessor(Arguments args) {
        this.args = args;
    }

    public static class Arguments {
        public int WeakCRJoinLimit = 4;
    }

    @Override
    public Result process(BasicObligation obl,
                          BasicObligationNode oblNode,
                          Abortion aborter,
                          RuntimeInformation rti) throws AbortionException {
        CriticalPairs cps = ProcessorUtil.getCP(obl);
        CPK localConfluence = cps.checkStatusDefinitive(args.WeakCRJoinLimit, aborter);
        return switch (localConfluence) {
            case WCR, WCR_DONE -> ResultFactory.unsuccessful("Termination Proof needed");
            case NOTCR -> ResultFactory.disproved(new NotCRProof(cps.getCounterExampleCR()));
            case NOTWCR -> ResultFactory.disproved(new NotWCRProof(cps.getCounterExampleWCR()));
            case MAYBE -> ResultFactory.unsuccessful("limited locally confluence without result");
        };
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof ConfTRSProblem;
    }

}
