package aprove.verification.confluence;

import java.util.*;
import java.util.Map.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.ExecutableStrategies.*;
import aprove.verification.confluence.Utility.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.Pair;
import immutables.ImmutableList;

public class StrongConfluenceProcessor implements Processor {
    public class StrongConfluenceProof extends DefaultProof {
        private Collection<String> found;
        
        public StrongConfluenceProof(Map<CriticalPairInfo, Pair<ImmutableList<RewriteStep>, ImmutableList<RewriteStep>>> found) {
            this.found = found.entrySet().stream()
                    .map(StrongConfluenceProof::eas)
                    .toList();
        }
        
        private static String eas(Entry<CriticalPairInfo, Pair<ImmutableList<RewriteStep>, ImmutableList<RewriteStep>>> e) {
            CriticalPairInfo k = e.getKey();
            TRSTerm d = k.divergence();
            TRSTerm s = k.s();
            TRSTerm t = k.t();
            TRSTerm v = e.getValue().getValue().getLast().substitutedTerm();
            return d + " -> <" + s  + ", " + t +"> ->= " + v;
        }
        @Override
        public String export(Export_Util o, VerbosityLevel level) {
            StringBuilder s = new StringBuilder();
            s.append(o.export("All Critical Pairs of the TRS R are strongly joinable:"));
            s.append(o.set(found, Export_Util.RULES));
            s.append(o.export("As R is also linear, this means R is strong confluent, which implies confluence. "));
            s.append(o.cite(Citation.BN98));
            return s.toString();
        }
    }

    @Override
    public Result process(BasicObligation obl,
                          BasicObligationNode oblNode,
                          Abortion aborter,
                          RuntimeInformation rti) throws AbortionException {
        ConfTRSProblem conftrs = (ConfTRSProblem) obl;
        CriticalPairs cps = conftrs.getCriticalPairs();
        if (conftrs.isLinear() &&
            cps
                   .areAllCriticalPairsStronglyJoinable(aborter)
                   .toBool()) {
            Map<CriticalPairInfo, Pair<ImmutableList<RewriteStep>, ImmutableList<RewriteStep>>> m = cps.getFoundJoinable();
            return ResultFactory.provedWithValueAndImplication(YNM.YES, YNMImplication.SOUND, new StrongConfluenceProof(m));
        }
        return ResultFactory.unsuccessful();
    }

    @Override
    public boolean isApplicable(BasicObligation obl) {
        if(obl instanceof ConfTRSProblem conftrs) {
            return conftrs.isLinear();
        }
        return false;
    }

}
