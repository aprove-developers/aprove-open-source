package aprove.verification.probabilistic.Complexity.ADPProblem;

import aprove.prooftree.Export.Utility.*;

/**
 * @author J-C Kassing & Leon Spitzer
 * @version $Id$
 */
public enum ADP_Cpx_Transformation {

        Instantiation("instantiating", Citation.KASSING_DISS),
        ForwardInstantiation("forward instantiating", Citation.KASSING_DISS),
        RuleOverlapInstantiation("rule overlap instantiation", Citation.KASSING_DISS),
        Rewriting("rewriting", Citation.KASSING_DISS),
        Narrowing("narrowing", Citation.KASSING_DISS);

    private final String predicate;
    private final Citation citation;

    private ADP_Cpx_Transformation(final String predicate, final Citation citation) {
        this.predicate = predicate;
        this.citation = citation;
    }

    public String getPredicate() {
        return this.predicate;
    }

    public Citation getCitation() {
        return this.citation;
    }

}
