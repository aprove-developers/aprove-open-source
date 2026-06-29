package aprove.verification.confluence;

import aprove.verification.dpframework.BasicStructures.Position;
import aprove.verification.dpframework.BasicStructures.Rule;
import aprove.verification.dpframework.BasicStructures.TRSTerm;

public record RewriteStep(TRSTerm originalTerm, Position position, Rule appliedRule, TRSTerm substitutedTerm) { }
