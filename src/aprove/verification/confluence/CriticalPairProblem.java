package aprove.verification.confluence;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.ProofPurposeDescriptors.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.strategies.Abortions.*;
import aprove.verification.confluence.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.xml.*;
import immutables.*;


public class CriticalPairProblem extends DefaultBasicObligation {
    
    private final CriticalPairs critPairs;
    private final List<CriticalPairInfo> critPairsInfo;
    private final ImmutableSet<Rule> R;
    private final ImmutableSet<FunctionSymbol> signature;
    
    
    public CriticalPairs getCriticalPairs() {
        return this.critPairs;
    }
    
    public CriticalPairProblem(final ConfTRSProblem conftrs, Abortion aborter) {
        this(conftrs.getRules(), conftrs.getCriticalPairs(), aborter);
    }
    
    public CriticalPairProblem(final ImmutableSet<Rule> R,
                               final Map<FunctionSymbol, ? extends Set<? extends GeneralizedRule>> ruleMap,
                               Abortion aborter) {
        this(R, new CriticalPairs(R, ruleMap), aborter);
    }
    
    public CriticalPairProblem(final ImmutableSet<Rule> R,
                               final CriticalPairs critPairs,
                               Abortion aborter) {
        super("Confluence CriticalPairs", "Confluence of Critical Pairs");
        this.critPairs = critPairs;
        this.critPairsInfo = critPairs.getAllFoundCriticalPairs(aborter);
        this.R = R;
        Set<FunctionSymbol> signature = CollectionUtils.getFunctionSymbols(this.R);
        this.signature = ImmutableCreator.create(signature);
    }
    
    public List<String> returnCritialPairs() {
        List<String> t = new ArrayList<String>();
        for (CriticalPairInfo cpi : this.critPairsInfo) {
            t.add(cpi.divergence() + " -> <" + cpi.s() + ", " + cpi.t() + ">");
        }
        return t;
    }

    @Override
    public String getStrategyName() {
        return "critical_pair_analysis";
    }

    @Override
    public ProofPurposeDescriptor getProofPurposeDescriptor() {
        return new DefaultProofPurposeDescriptor(this, "This class is a wrapper for confluence related proofs of critical pairs");
    }

    @Override
    public String export(Export_Util o) {
        final StringBuilder s = new StringBuilder();
        s.append(o.export("Critical Pair Analysis for confluence of TRS R"));
        s.append(o.cond_linebreak());
        if (this.R.isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The TRS R consists of the following TRS:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.R, Export_Util.RULES));
            s.append(o.cond_linebreak());
        }
        if (this.critPairsInfo.isEmpty()) {
            s.append("R is empty.");
            s.append(o.linebreak());
        } else {
            s.append(o.export("The following critical Pairs are made:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.returnCritialPairs(), Export_Util.RULES));
            s.append(o.cond_linebreak());
        }

        s.append(o.linebreak());

        return s.toString();
    }

    @Override
    public String toString() {
        return this.export(new PLAIN_Util());
    }


    @Override
    public Element toDOM(final Document doc, final XMLMetaData xmlMetaData) {
        final Element e = XMLTag.QTRS_OBL.createElement(doc);
        final Element f = XMLTag.QTRS.createElement(doc);

        final Element trs = XMLTag.TRS.createElement(doc);
        CollectionUtils.addChildren(this.R, trs, doc, xmlMetaData);
        f.appendChild(trs);

        final Element sig = XMLTag.SIGNATURE.createElement(doc);
        CollectionUtils.addChildren(this.signature, sig, doc, xmlMetaData);
        f.appendChild(sig);

        e.appendChild(f);
        return e;
    }

    @Override
    public Element getCPFInput(final Document doc, final XMLMetaData xmlMetaData, final TruthValue tv) {
        final Element trsInput = CPFTag.TRS_INPUT.create(doc,
                                                         CPFTag.trs(doc, xmlMetaData, this.R));

        final Element strategy = CPFTag.STRATEGY.createElement(doc);

        return trsInput;
    }
    /* (non-Javadoc)
     * @see aprove.ProofTree.Obligations.BasicObligation.DefaultBasicObligation#offersCertifiableTechniques()
     */
    @Override
    public boolean offersCertifiableTechniques() {
        return false;
    }
    

}
