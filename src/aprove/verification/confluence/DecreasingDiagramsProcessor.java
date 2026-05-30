/*package aprove.verification.confluence;

import aprove.prooftree.Obligations.BasicObligation;
import aprove.prooftree.Obligations.BasicObligationNode;
import aprove.strategies.Abortions.Abortion;
import aprove.strategies.Abortions.AbortionException;
import aprove.strategies.Annotations.NoParams;
import aprove.strategies.ExecutableStrategies.RuntimeInformation;
import aprove.verification.dpframework.Processor;
import aprove.verification.dpframework.Result;
import aprove.verification.dpframework.ResultFactory;
import aprove.verification.oldframework.Logic.YNMImplication;

import java.util.List;

@NoParams
public class DecreasingDiagramsProcessor implements Processor {
    @Override
    public Result process(BasicObligation obl, BasicObligationNode oblNode, Abortion aborter, RuntimeInformation rti) throws AbortionException {
        ConfTRSProblem confTrsProblem = (ConfTRSProblem) obl;
        CriticalPairProblem criticalPairProblem = new CriticalPairProblem(confTrsProblem, aborter);
        DecreasingDiagramProblem decreasingDiagramProblem = new DecreasingDiagramProblem(confTrsProblem);
        // TODO: This creates a new node, we want to just replace the current node with an AND junctor node
        return ResultFactory.provedAnd(List.of(criticalPairProblem, decreasingDiagramProblem), YNMImplication.SOUND, new DecreasingDiagramProof(null));
        //ResultFactory.provedAndFromOblNodes(listOfProblemNodes, YNMImplication.SOUND, proof);
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        return obl instanceof ConfTRSProblem;
    }
}
*/