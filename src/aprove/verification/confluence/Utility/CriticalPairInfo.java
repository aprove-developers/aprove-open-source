package aprove.verification.confluence.Utility;


import aprove.verification.dpframework.BasicStructures.*;

public record CriticalPairInfo(GeneralizedRule sRule,
                               GeneralizedRule tRule,
                               TRSTerm s,
                               TRSTerm t,
                               boolean isRootOverlap,
                               TRSTerm divergence,
                               Position p) {
    public boolean isTrivial() {
        return s.equals(t);
    }
}
