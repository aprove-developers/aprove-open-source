package aprove.prooftree.Export.Utility;

/**
 * Citations for the techniques used by AProVE to show termination.
 * This file ought to be kept in sync with literatur.bib (in the same package).
 *
 * @version $Id$
 */
public enum Citation {
    AG00,
    RPO, // TODO
    MATRO, // TODO
    DA_FALKE, // TODO
    CS_FR,  // TODO
    MATCHBOUNDS1,  // TODO
    MATCHBOUNDS2,  // TODO
    TAB_LEFTLINEAR, // TODO
    TAB_NONLEFTLINEAR, // TODO
    AAECCNOC,  // TODO
    GK01, // TODO
    CS_Inn,  // TODO
    CS_Term, // TODO
    @Deprecated
    UNKNOWN,
    CONREM, // TODO
    JAR06,  // TODO
    LPAR04, // TODO
    HASKELL, // TODO
    FROCOS05, // TODO
    NONINF, // TODO
    NOC, // TODO
    SUBTERM_CRITERION, // TODO
    NEGPOLO, // TODO
    EDGSTAR, // TODO
    LPO, // TODO
    KBO, // TODO
    POLO, // TODO
    CS_Luc, // TODO
    DIRECT_TERMINATION, // TODO
    CTRS, // TODO
    ACRPOS, // TODO
    LOPSTR, // TODO
    DA_STEIN,
    AAECC05, // TODO
    SEMLAB, // TODO
    CS_Zan, // TODO
    RATPOLO,
    ROOTLAB,
    ARCTIC, // TODO
    QKBO,
    MAXPOLO,
    GM04,
    LPAR08,
    DA_EMMES,
    DA_SWIDERSKI,
    REDRHS,
    REVERSE,
    RIGHTGROUND,
    THIEMANN,
    PROLOG, //TODO
    ENDRULLIS, // see http://joerg.endrullis.de/jamboxTheorems06.html
    BD86,
    GESER,
    THIEMANN_LOOPS_UNDER_STRATEGIES,
    SG07, // see http://www.logic.at/staff/gramlich/papers/wst07.pdf
    NHAMHZ_LPAR08, // see http://cl-informatik.uibk.ac.at/research/publications/2008/uncurrying-for-termination-2/#
    CSRT_FROCOS11,
    OPPELT08,
    ENDRULLIS_HENDRIKS_2009,
    DT09,
    DT10,
    ICLP10,
    TOCL09,
    NONLOOP,
    STERNAGEL_THIEMANN_RTA14,
    ADY19, 
    KASSING_MA,
    CADE23,
    FoSSaCS24,
    FLOPS24,
    VARTANYAN_BA,  // TODO
    IJCAR24, // TODO
    FLOPS24JOURNAL,// TODO
    EY09,
    EGK13,
    // Confluence
    KB70,
    HUE80,
    NEW42,
    OHL94A,
    OHL94B,
    TOY87,
    RV80,
    BN98
    ;

    @Override
    public String toString() {
        return this.name();
    }
}
