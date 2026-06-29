package aprove.verification.confluence.Utility;


import aprove.verification.dpframework.BasicStructures.*;

public record CriticalPairInfo(
        Rule sRule,
        Rule tRule,
        TRSTerm s,
        TRSTerm t,
        boolean isRootOverlap,
        TRSTerm divergence,
        Position p) {
    public boolean isTrivial() {
        return s.equals(t);
    }
}
