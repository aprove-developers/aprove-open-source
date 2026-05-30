package aprove.verification.confluence;

import java.util.*;

import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.confluence.Utility.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.Pair;
import immutables.ImmutableList;


public class LocalConfluenceProcessor implements Processor {
    
    @Override
    public Result process(BasicObligation obl,
                          BasicObligationNode oblNode,
                          Abortion aborter,
                          RuntimeInformation rti) throws AbortionException {
        CriticalPairs cps = ProcessorUtil.getCP(obl);
        
        if (cps.isNonOverlapping(aborter)) {
            return ResultFactory.proved(new WCRProof(null));
        }
        CPK localConfluence = cps.checkStatusWeak(aborter);
        switch(localConfluence) {
            case WCR:
            case WCR_DONE:
                Map<CriticalPairInfo, Pair<ImmutableList<RewriteStep>, ImmutableList<RewriteStep>>> m = cps.getFoundJoinable();
                return ResultFactory.proved(new WCRProof(m));
            case NOTCR:
                return ResultFactory.disproved(new NotCRProof(cps.getCounterExampleCR()));
            case NOTWCR:
                return ResultFactory.disproved(new NotWCRProof(cps.getCounterExampleWCR()));
            case MAYBE:
                return ResultFactory.error("local confluence analysis too deep");
            default:
                return ResultFactory.error("local confluence algorithm returned null.");
        }
    }
    

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof ConfTRSProblem || obl instanceof CriticalPairProblem;
    }

}
