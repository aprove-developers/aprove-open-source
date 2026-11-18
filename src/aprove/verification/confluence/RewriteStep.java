package aprove.verification.confluence;

import aprove.verification.dpframework.BasicStructures.Position;
import aprove.verification.dpframework.BasicStructures.Rule;
import aprove.verification.dpframework.BasicStructures.TRSTerm;

/**
 * Represents a rewrite step for a TRS.
 * @param originalTerm The term before substitution.
 * @param position The position in the original term to which subterm the rule has been applied to.
 * @param appliedRule The rule applied to the original term.
 * @param substitutedTerm The resulting term after the substitution.
 */
public record RewriteStep(TRSTerm originalTerm, Position position, Rule appliedRule, TRSTerm substitutedTerm) { }
