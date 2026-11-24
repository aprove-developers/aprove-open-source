package aprove.verification.confluence;

import java.util.*;
import java.util.Map.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.verification.confluence.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.Pair;
import immutables.ImmutableList;

public class WCRProof extends DefaultProof {
    
    private final Collection<String> found;

    public WCRProof(final Map<CriticalPairInfo, Pair<ImmutableList<RewriteStep>, ImmutableList<RewriteStep>>> found) {
        if (found == null) {
            this.found = Collections.emptyList();
            return;
        }
        this.found = found.entrySet().stream()
                .map(WCRProof::eas)
                .toList();
    }
    
    private static String eas(Entry<CriticalPairInfo, Pair<ImmutableList<RewriteStep>, ImmutableList<RewriteStep>>> e) {
        CriticalPairInfo k = e.getKey();
        TRSTerm d = k.divergence();
        TRSTerm s = k.s();
        TRSTerm t = k.t();
        TRSTerm v = e.getValue().getValue().getLast().substitutedTerm();
        return d + " -> <" + s  + ", " + t +"> ->* " + v;
    }
    @Override
    public String export(Export_Util o, VerbosityLevel level) {
        StringBuilder s = new StringBuilder();
        s.append(o.export("All Critical Pairs of the TRS R are joinable"));
        if (found.isEmpty()) {
            s.append(o.export(", as R has no critical pairs."));
            s.append(o.cond_linebreak());
            s.append(o.linebreak());
        }
        else {
            s.append(o.export(":"));
            s.append(o.set(found, Export_Util.RULES));
        }
        
        s.append(o.export("Therefore R fulfills WCR (local confluence). "));
        s.append(o.cite(Citation.KB70));
        return s.toString();
    }
    
}