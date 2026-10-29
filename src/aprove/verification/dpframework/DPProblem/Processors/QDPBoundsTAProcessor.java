package aprove.verification.dpframework.DPProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.BasicStructures.Matchbounds.*;
import aprove.verification.dpframework.BasicStructures.Matchbounds.TRSBounds.*;
import aprove.verification.dpframework.BasicStructures.Matchbounds.TRSBoundsHelper.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.xml.*;
import immutables.*;

/**
 * @author Marcel Klinzing
 */
public class QDPBoundsTAProcessor extends QDPProblemProcessor {

    TRSBounds.STAStrategy sTAS;
    TRSBounds.ConflictResolvingStrategy cRS;
    TRSBounds.WhenToBuildTAStrategy wTBTA;
    TRSBounds.QuasiDetStrategy qDS;

    final int mCTR; // MAX_CONFLICTS_TO_RESOLVE
    final int mTOA; // MAX_TRANSITIONS_OF_A
    final int mSOA; // MAX_STATES_OF_A

    @ParamsViaArgumentObject
    public QDPBoundsTAProcessor(final Arguments arguments) {
        this.sTAS = arguments.sTAS;
        this.cRS = arguments.cRS;
        this.wTBTA = arguments.wTBTA;
        this.qDS = arguments.qDS;
        this.mCTR = arguments.MAX_CONFLICTS_TO_RESOLVE;
        this.mTOA = arguments.MAX_TRANSITIONS_OF_A;
        this.mSOA = arguments.MAX_STATES_OF_A;
    }

    @Override
    public boolean isQDPApplicable(final QDPProblem qdp) {
        if (Options.certifier.isCeta()) {
            return false;
        }
        if (!qdp.getMinimal()) {
            // the bounds start language covers only rule-generated instantiations,
            // so the technique argues about minimal chains only
            return false;
        }
        final Set<Rule> P = qdp.getP();
        final Set<FunctionSymbol> rootsOfP = new LinkedHashSet<FunctionSymbol>();
        for (final Rule r : P) {
            final TRSFunctionApplication lhs = r.getLeft();
            rootsOfP.add(lhs.getRootSymbol());
            final TRSTerm rhs = r.getRight();
            if (!rhs.isVariable()) {
                final TRSFunctionApplication fARhs = (TRSFunctionApplication) rhs;
                rootsOfP.add(fARhs.getRootSymbol());
            }
        }

        // check if any root symbol of P occurs in proper subterms of the rules in P
        for (final Rule r : P) {
            final TRSFunctionApplication lhs = r.getLeft();
            for (final TRSTerm t : lhs.getArguments()) {
                for (final FunctionSymbol f : t.getFunctionSymbols()) {
                    if (rootsOfP.contains(f)) {
                        return false;
                    }
                }
            }

            final TRSTerm rhs = r.getRight();
            if (!rhs.isVariable()) {
                final TRSFunctionApplication fARhs = (TRSFunctionApplication) rhs;
                for (final TRSTerm t : fARhs.getArguments()) {
                    for (final FunctionSymbol f : t.getFunctionSymbols()) {
                        if (rootsOfP.contains(f)) {
                            return false;
                        }
                    }
                }
            }
        }

        final Set<Rule> R = qdp.getR();
        for (final FunctionSymbol f : CollectionUtils.getFunctionSymbols(R)) {
            if (rootsOfP.contains(f)) {
                return false;
            }
        }

        return true;
    }

    @Override
    protected Result processQDPProblem(final QDPProblem qdp, final Abortion aborter) throws AbortionException {
        if (Globals.useAssertions) {
            assert (!qdp.getP().isEmpty());
        }

        final Set<Rule> P = qdp.getP();
        final Rule ruleToRemove = P.iterator().next(); // safe since P is not empty
        final Set<Rule> R = qdp.getR();
        final boolean leftLinear = CollectionUtils.isLeftLinear(R) && CollectionUtils.isLeftLinear(P);
        final boolean isNotDuplicating = this.isNonDuplicating(R) && this.isNonDuplicating(P);
        final boolean isRightlinear = CollectionUtils.isRightLinear(R) && CollectionUtils.isRightLinear(P);
        aborter.checkAbortion();

        boolean useRFC;
        if (isRightlinear) {
            useRFC = true;
        } else {
            useRFC = false;
        }

        final Set<Rule> usableRulesOfR = new LinkedHashSet<Rule>();
        usableRulesOfR.addAll(qdp.getUsableRules());

        if (!isNotDuplicating) {
            final Set<FunctionSymbol> fS = new LinkedHashSet<FunctionSymbol>();
            fS.addAll(CollectionUtils.getFunctionSymbols(usableRulesOfR));
            fS.addAll(CollectionUtils.getFunctionSymbols(P));

            final TRSBoundsHelper.FunctionSymbolGenerator funcSymbGen = new FunctionSymbolGenerator(fS);
            final FunctionSymbol c = funcSymbGen.getFresh("c_ur", 2);
            final TRSVariable x = TRSTerm.createVariable("x");
            final TRSVariable y = TRSTerm.createVariable("y");

            final ArrayList<TRSTerm> args = new ArrayList<TRSTerm>();
            args.add(x);
            args.add(y);
            final TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(c, args);
            usableRulesOfR.add(Rule.create(lhs, x));
            usableRulesOfR.add(Rule.create(lhs, y));
        }

        TRSBounds b = null;
        TRSBounds.Certificate certificate = null;
        if (leftLinear) {
            //create compatible TA
            if (isNotDuplicating) {
                b = new TRSBounds(usableRulesOfR, P, ruleToRemove, TRSBounds.Bound.MATCHDP, this.sTAS, this.cRS, this.wTBTA, this.mCTR, this.mTOA,
                                this.mSOA, useRFC);
            } else {
                b = new TRSBounds(usableRulesOfR, P, ruleToRemove, TRSBounds.Bound.TOPDP, this.sTAS, this.cRS, this.wTBTA, this.mCTR, this.mTOA,
                                this.mSOA, useRFC);
            }
        } else {
            //create quasi-deterministic, raise-consistent, quasi-compatible TA
            if (isNotDuplicating) {
                b = new TRSBounds(usableRulesOfR, P, ruleToRemove, TRSBounds.Bound.MATCHRAISEDP, this.sTAS, this.cRS, this.wTBTA, this.qDS,
                                this.mCTR, this.mTOA, this.mSOA, useRFC);
            } else {
                b = new TRSBounds(usableRulesOfR, P, ruleToRemove, TRSBounds.Bound.TOPRAISEDP, this.sTAS, this.cRS, this.wTBTA, this.qDS, this.mCTR,
                                this.mTOA, this.mSOA, useRFC);

            }

        }
        certificate = b.getCertificate(aborter);

        if (certificate != null) {
            return this.processQDPProblem(qdp, R, P, ruleToRemove, usableRulesOfR, certificate);
        } else {
            return ResultFactory.unsuccessful();
        }
    }

    private Result processQDPProblem(final QDPProblem qdp, final Set<Rule> R, final Set<Rule> P, final Rule ruleToRemove, final Set<Rule> usableRulesOfR,
                    final TRSBounds.Certificate certificate) {
        final Set<Rule> newP = new LinkedHashSet<Rule>(P);
        newP.remove(ruleToRemove);
        final QDPProblem newQDP = qdp.getSubProblem(ImmutableCreator.create(newP));
        final Proof proof = new QDPBoundsTAProof(ruleToRemove, usableRulesOfR, certificate, qdp, newQDP);
        return ResultFactory.proved(newQDP, YNMImplication.EQUIVALENT, proof);
    }

    private class QDPBoundsTAProof extends QDPProof {

        private final TRSBounds.Certificate certificate;
        private final Set<Rule> rulesToRemove;
        private final Set<Rule> usableRules;
        private final QDPProblem origQDP;
        private final QDPProblem newQDP;

        public QDPBoundsTAProof(final Rule ruleToRemove, final Set<Rule> usableRules, final Certificate certificate,
                final QDPProblem origQDP, final QDPProblem newQDP) {
            this.rulesToRemove = new LinkedHashSet<Rule>();
            this.rulesToRemove.add(ruleToRemove);
            this.usableRules = usableRules;
            this.certificate = certificate;
            this.newQDP = newQDP;
            this.origQDP = origQDP;
        }

        /**
         * Returns the output string.
         */
        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder result = new StringBuilder();
            String typeOfBound = "";
            if (this.certificate.getBound() == TRSBounds.Bound.TOPDP || this.certificate.getBound() == TRSBounds.Bound.TOPRAISEDP) {
                typeOfBound = "Top-";
            } else if (this.certificate.getBound() == TRSBounds.Bound.MATCHDP || this.certificate.getBound() == TRSBounds.Bound.MATCHRAISEDP) {
                typeOfBound = "Match-";
            }
            if (this.certificate.getBound() == TRSBounds.Bound.TOPRAISEDP || this.certificate.getBound() == TRSBounds.Bound.MATCHRAISEDP) {
                typeOfBound += "(raise-)";
            }

            typeOfBound += "DP-";

            result.append("The DP-Problem (P, R) could be shown to be " + typeOfBound + "Bounded "
                            + o.cite(new Citation[] {Citation.TAB_NONLEFTLINEAR }) + " by " + this.certificate.getBoundedBy() + " for the Rule: "
                            + o.set(this.rulesToRemove, Export_Util.RULES) + "by considering the usable rules: ");

            result.append(o.linebreak());
            result.append(o.set(this.usableRules, Export_Util.RULES));
            result.append(o.linebreak());
            /*result.append("The tree automaton used to show the " + typeOfBound + "Boundedness consists of "
                    + this.certificate.getTreeAutomaton().getTransitions()
                            .size()
                    + " transitions and of which there are "
                    + this.certificate.getTreeAutomaton().getEpsTransitions()
                            .size()
                    + " epsilon transitions and "
                    +
                + this.certificate.getTreeAutomaton().getAllStates().size() + " states.");*/
            result.append("The compatible tree automaton used to show the " + typeOfBound + "Boundedness is represented by: ");
            result.append(o.linebreak());
            this.certificate.printTA(o, result);

            return result.toString();
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            if (modus.isPositive()) {
                return super.toCPF(doc, childrenProofs, xmlMetaData, modus);
            } else {
                return super.ruleRemovalNontermProof(doc, childrenProofs[0], xmlMetaData, this.newQDP);
            }
        }


        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return !modus.isPositive();
        }

    }

    private boolean isNonDuplicating(final Set<Rule> R) {
        boolean isNonDuplicating = true;
        for (final Rule r : R) {

            if (r.isDuplicating()) {
                isNonDuplicating = false;
            }
        }
        return isNonDuplicating;
    }

    public static class Arguments {
        public TRSBounds.STAStrategy sTAS = TRSBounds.STAStrategy.RC_SPLIT;
        public TRSBounds.ConflictResolvingStrategy cRS = TRSBounds.ConflictResolvingStrategy.KMS;
        public TRSBounds.WhenToBuildTAStrategy wTBTA = TRSBounds.WhenToBuildTAStrategy.BUILD_TA_AFTER_RESOLVING_ONE_CONFLICT;
        public TRSBounds.QuasiDetStrategy qDS = TRSBounds.QuasiDetStrategy.APPROX;
        public int MAX_CONFLICTS_TO_RESOLVE = 10000;
        public int MAX_TRANSITIONS_OF_A = 10000;
        public int MAX_STATES_OF_A = 4000;
    }
}
