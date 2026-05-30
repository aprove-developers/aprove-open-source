package aprove.verification.confluence;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.verification.confluence.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;


public class NotCRProof extends DefaultProof {
    private final JoinableResult.NonConfluent nonConfluentResult;

    NotCRProof(JoinableResult.NonConfluent nonConfluentResult) {
        this.nonConfluentResult = nonConfluentResult;
    }

    @Override
    public String export(Export_Util o, VerbosityLevel level) {
        return o.export("The TRS is not confluent:") +
                o.cond_linebreak() +
                o.export("The following term leads to following normal forms:") +
                o.cond_linebreak() +
                o.cond_linebreak() +
                o.export(nonConfluentResult.leftNormalForm().getFirst().originalTerm()) +
                o.linebreak() +
                o.export("->* ") +
                o.export(nonConfluentResult.leftNormalForm().getLast().substitutedTerm()) +
                o.linebreak() +
                o.export("->* ") +
                o.export(nonConfluentResult.rightNormalForm().getLast().substitutedTerm());
    }
}
