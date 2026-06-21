package aprove.api.details.impl;

import java.util.*;
import java.util.stream.*;

import aprove.api.details.*;
import aprove.prooftree.Obligations.*;
import aprove.prooftree.Proofs.*;

public enum Details {
    ;

    private static final Map<Capability, BaseDetails<?>> details = createDetails();

    private static Map<Capability, BaseDetails<?>> createDetails() {
        Map<Capability, BaseDetails<?>> result = new LinkedHashMap<>();
        result.put(Capability.HTML, new HtmlDetails());
        result.put(Capability.PLAIN, new PlainDetails());
        result.put(Capability.SOURCE, new SourceDetails());
        result.put(Capability.DOT, new DotDetails());
        result.put(Capability.LATEX, new LatexDetails());
        result.put(Capability.DOT_MODERN, new DotModernDetails());
        result.put(Capability.SVG, new SVGDetails());
        return result;
    }

    private static Object getBasicObligationOrNode(ObligationNode obligationNode) {
        if (obligationNode instanceof BasicObligationNode) {
            BasicObligationNode basicObligationNode = (BasicObligationNode) obligationNode;
            return basicObligationNode.getBasicObligation();
        } else {
            return obligationNode;
        }
    }

    public static Set<Capability> getCapabilities(Proof proof) {
        return Details.doGetCapabilities(proof);
    }

    public static Set<Capability> getCapabilities(ObligationNode obligationNode) {
        return Details.doGetCapabilities(getBasicObligationOrNode(obligationNode));
    }

    private static Set<Capability> doGetCapabilities(Object o) {
        return Details.details.entrySet()
                              .stream()
                              .filter(e -> e.getValue().isSupported(o))
                              .map(e -> e.getKey())
                              .collect(Collectors.toSet());
    }

    public static Detail getDetail(Capability capability, Proof proof) {
        return Details.doGetDetail(capability, proof);
    }

    public static Detail getDetail(Capability capability, ObligationNode obligationNode) {
        return Details.doGetDetail(capability, getBasicObligationOrNode(obligationNode));
    }

    private static Detail doGetDetail(Capability capability, Object o) {
        BaseDetails<?> d = Details.details.get(capability);
        if (d != null) {
            return DetailImpl.valid(capability, d.getDetails(o));
        } else {
            return DetailImpl.invalid(capability);
        }
    }
}
