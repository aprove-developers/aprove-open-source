package aprove.verification.confluence;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.verification.confluence.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


public class NotCRProof extends DefaultProof {
    private final TRSTerm divergence;
    private final TRSTerm s;
    private final TRSTerm t;

    public NotCRProof(JoinableResult.NonConfluent nonConfluentResult) {
        this.divergence = nonConfluentResult.leftNormalForm().getFirst().originalTerm();
        this.s = nonConfluentResult.leftNormalForm().getLast().substitutedTerm();
        this.t = nonConfluentResult.rightNormalForm().getLast().substitutedTerm();
    }

    public NotCRProof(TRSTerm divergence, TRSTerm s, TRSTerm t) {
        this.divergence = divergence;
        this.s = s;
        this.t = t;
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {
        return o.export("The TRS is not confluent:") +
                o.cond_linebreak() +
                o.export("The following term leads to following normal forms:") +
                o.cond_linebreak() +
                o.cond_linebreak() +
                o.export(divergence) +
                o.linebreak() +
                o.export("->* ") +
                o.export(s) +
                o.linebreak() +
                o.export("->* ") +
                o.export(t);
    }
}
