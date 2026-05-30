package aprove.verification.confluence;

import aprove.verification.dpframework.BasicStructures.GeneralizedRule;
import aprove.verification.dpframework.BasicStructures.Position;
import aprove.verification.dpframework.BasicStructures.TRSTerm;

public record RewriteStep(TRSTerm originalTerm, Position position, GeneralizedRule appliedRule, TRSTerm substitutedTerm) {
}
