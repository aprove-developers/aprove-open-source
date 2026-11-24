package aprove.verification.confluence;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.confluence.Utility.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;


public class LocalConfluenceProcessor implements Processor {

    @Override
    public Result process(BasicObligation obl,
                          BasicObligationNode oblNode,
                          Abortion aborter,
                          RuntimeInformation rti) throws AbortionException {
        CriticalPairs cps = ProcessorUtil.getCP(obl);

        if (cps.isNonOverlapping(aborter))
            return ResultFactory.proved(new WCRProof(null));

        CPK localConfluence = cps.checkStatusWeak(aborter);
        return switch (localConfluence) {
            case WCR, WCR_DONE -> ResultFactory.proved(new WCRProof(cps.getFoundJoinable()));
            case NOTCR -> ResultFactory.disproved(new NotCRProof(cps.getCounterExampleCR()));
            case NOTWCR -> ResultFactory.disproved(new NotWCRProof(cps.getCounterExampleWCR()));
            case MAYBE -> ResultFactory.error("local confluence analysis too deep");
        };
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof CriticalPairProblem;
    }
}
