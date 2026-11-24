package aprove.verification.confluence;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.verification.confluence.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.ImmutableList;


public class NotCRProof extends DefaultProof {
    private final TRSTerm divergence;
    private final TRSTerm s;
    private final TRSTerm t;

    private final ImmutableList<RewriteStep> leftSequence;
    private final ImmutableList<RewriteStep> rightSequence;

    private final boolean distinctNormalForms;

    public NotCRProof(JoinableResult.NonConfluent nonConfluentResult) {
        this.leftSequence = nonConfluentResult.leftNormalForm();
        this.rightSequence = nonConfluentResult.rightNormalForm();
        this.divergence = leftSequence.getFirst().originalTerm();
        this.s = leftSequence.getLast().substitutedTerm();
        this.t = rightSequence.getLast().substitutedTerm();
        this.distinctNormalForms = true;
    }

    public NotCRProof(TRSTerm divergence, TRSTerm s, TRSTerm t) {
        this.divergence = divergence;
        this.s = s;
        this.t = t;
        this.leftSequence = null;
        this.rightSequence = null;
        this.distinctNormalForms = false;
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {
        if (distinctNormalForms) {
            return o.export("The TRS is not confluent:") +
                    o.cond_linebreak() +
                    o.export("The following term can be reduced to two different normal forms:") +
                    o.cond_linebreak() +
                    o.cond_linebreak() +
                    exportSequence(o, leftSequence) +
                    o.linebreak() +
                    o.linebreak() +
                    exportSequence(o, rightSequence);
        }

        return o.export("The TRS is not confluent:") +
                o.cond_linebreak() +
                o.export("The following term can be reduced to two terms that are not joinable:") +
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

    private String exportSequence(Export_Util o, ImmutableList<RewriteStep> sequence) {
        StringBuilder sb = new StringBuilder();
        sb.append(o.export(sequence.getFirst().originalTerm()));
        for (RewriteStep step : sequence) {
            sb.append(o.linebreak());
            sb.append(o.export("-> "));
            sb.append(o.export(step.substitutedTerm()));
        }
        return sb.toString();
    }
}
