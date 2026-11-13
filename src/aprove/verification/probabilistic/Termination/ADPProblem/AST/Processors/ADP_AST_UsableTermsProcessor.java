package aprove.verification.probabilistic.Termination.ADPProblem.AST.Processors;

import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.ADPProblem.*;
import aprove.verification.probabilistic.Termination.ADPProblem.AST.*;

/**
 * Usable Terms Processor as described in Kassing's master's thesis, CADE23, and FLOPS24 for ADPs
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class ADP_AST_UsableTermsProcessor extends ADP_AST_ProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isAST_ADPApplicable(final ADP_AST_Problem qdp) {
        if (qdp.isBasic()) { /**BASIC**/
            // for the reachability component, all edges have to be regarded (the ADPs of I are not in an SCC)
            return qdp.getDependencyGraph().doUnusablePairsExist() || qdp.getReachDependencyGraph().doUnusablePairsExistOnAllEdges();
        } else { /**FULL and INNERMOST**/
            return qdp.getDependencyGraph().doUnusablePairsExist();
        }

    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processAST_ADPProblem(final ADP_AST_Problem qdp, final Abortion aborter) throws AbortionException {
        final Set<TRSFunctionApplication> unusableTermsSet = new HashSet<>();

        final ProbQDependencyGraph graph = qdp.getDependencyGraph();
        final ProbQDependencyGraph reachGraph = qdp.getReachDependencyGraph();

        final Set<ProbabilisticRule> P = qdp.getP();

        ADP_AST_Problem newProblem;
        final Set<ProbabilisticRule> newP = new HashSet<>();
        final Set<ProbabilisticRule> newReach = new HashSet<>();
        /**BASIC**/

        for (final ProbabilisticRule depTuple : P) {
            //Create new rhs
            final HashMultiSet<Pair<TRSTerm, BigFraction>> probabilityMap = new HashMultiSet<>();
            for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : depTuple.getRight().getProbabilityMapping().entrySet()) {
                final TRSTerm term = entry.getKey().getKey();
                final BigFraction prob = entry.getKey().getValue();
                final Integer amount = entry.getValue();

                //Create the term
                final Set<Position> positionsToRemoveAnnos = new HashSet<>();
                for (final Pair<TRSFunctionApplication, Position> termPositionPair : term.getAnnoSubtermsWithPositions(qdp.getDeAnnoMap())) {
                    if (graph.isUnusableTerm(termPositionPair.x)) {
                        positionsToRemoveAnnos.add(termPositionPair.y);
                        unusableTermsSet.add(termPositionPair.x);
                    }
                }
                final TRSTerm newTerm = term.renameAtAllMap(positionsToRemoveAnnos, qdp.getDeAnnoMap());

                probabilityMap.add(new Pair<>(newTerm, prob), amount);
            }
            final MultiDistribution<TRSTerm> rhs = MultiDistribution.create(probabilityMap);
            final ProbabilisticRule newDepTuple = ProbabilisticRule.create(depTuple.getLeft(), rhs);

            newP.add(newDepTuple);
        }

        if (qdp.isBasic()) {
            /**BASIC**/
            final Set<ProbabilisticRule> ReachADPs = qdp.getReach();
            // usability w.r.t. I u P, i.e., w.r.t. all edges of the reachability graph (not only within SCCs)
            final Set<TRSFunctionApplication> usableReachTerms = reachGraph.getUsableTermsOnAllEdges();

            for (final ProbabilisticRule depTuple : ReachADPs) {
                //Create new rhs
                final HashMultiSet<Pair<TRSTerm, BigFraction>> probabilityMap = new HashMultiSet<>();
                for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : depTuple.getRight().getProbabilityMapping().entrySet()) {
                    final TRSTerm term = entry.getKey().getKey();
                    final BigFraction prob = entry.getKey().getValue();
                    final Integer amount = entry.getValue();

                    //Create the term
                    final Set<Position> positionsToRemoveAnnos = new HashSet<>();
                    for (final Pair<TRSFunctionApplication, Position> termPositionPair : term.getAnnoSubtermsWithPositions(qdp.getDeAnnoMap())) {
                        if (!usableReachTerms.contains(termPositionPair.x.getStandardRenumbered())) {
                            positionsToRemoveAnnos.add(termPositionPair.y);
                            unusableTermsSet.add(termPositionPair.x);
                        }
                    }
                    final TRSTerm newTerm = term.renameAtAllMap(positionsToRemoveAnnos, qdp.getDeAnnoMap());

                    probabilityMap.add(new Pair<>(newTerm, prob), amount);
                }
                final MultiDistribution<TRSTerm> rhs = MultiDistribution.create(probabilityMap);
                final ProbabilisticRule newDepTuple = ProbabilisticRule.create(depTuple.getLeft(), rhs);

                newReach.add(newDepTuple);
            }
        }

        if (qdp.isBasic()) { /**BASIC**/
            newProblem = ADP_AST_Problem.createBasic(newP, newReach, qdp.getSwithQ(), qdp.getReachPQTRS(), qdp.getStrat(), qdp.getBiAnnoMap());
        } else { /**FULL and INNERMOST**/
            newProblem = ADP_AST_Problem.create(newP, qdp.getSwithQ(), qdp.getStrat(), qdp.getBiAnnoMap());
        }

        final AST_ADPUsableTermsProof UPPproof = new AST_ADPUsableTermsProof(qdp, unusableTermsSet);

        final Result result = ResultFactory.proved(newProblem, YNMImplication.EQUIVALENT, UPPproof);
        return result;
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class AST_ADPUsableTermsProof extends ADP_AST_Proof {

        private final ADP_AST_Problem origPQDP;
        private final Set<TRSFunctionApplication> unusableTermsSet;

        private AST_ADPUsableTermsProof(final ADP_AST_Problem origObl,
            final Set<TRSFunctionApplication> unusableTermsSet) {
            this.origPQDP = origObl;
            this.unusableTermsSet = unusableTermsSet;
        }

        private static final Citation[] citations = new Citation[] { Citation.LPAR04,
            Citation.FROCOS05,
            Citation.EDGSTAR };

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();
            res.append(o.paragraph());
            if (!this.origPQDP.isBasic()) { //innermost and full AST
                res.append("We use the usable terms processor ").append(o.cite(Citation.KASSING_DISS)).append(".");
            } else { //basic AST
                res.append("We use the usable terms processor ").append(o.cite(Citation.JPK60)).append(".");
            }
            res.append(o.linebreak());
            res.append("The approximation of the Dependency Graph ")
                .append(o.cite(AST_ADPUsableTermsProof.citations))
                .append(" gives us the following unusable Terms: ");
            res.append(o.linebreak());
            res.append(this.unusableTermsSet.toString());
            res.append(o.linebreak());
            res.append("Hence, we can remove the annotations from these terms from every RHS of every ADP");

            return o.export(res.toString());
        }

    }

}
