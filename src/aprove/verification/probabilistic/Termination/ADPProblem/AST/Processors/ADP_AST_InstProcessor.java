package aprove.verification.probabilistic.Termination.ADPProblem.AST.Processors;

import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;

import aprove.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.ADPProblem.AST.*;

/**
 * The instantiation processor for ADPS as described in journal paper of FLOPS24
 *
 * @author J-C Kassing
 */
public class ADP_AST_InstProcessor extends ADP_AST_TransformationProcessor {

    @ParamsViaArgumentObject
    public ADP_AST_InstProcessor(final ADP_AST_TransformationProcessor.Arguments arguments) {
        super(ADP_AST_Transformation.Instantiation, arguments);
    }

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isAST_ADPApplicable(final ADP_AST_Problem qdp) {
        if (this.initialADPs || qdp.isBasic()) { //Does not work for basic problems (I,P), see the super class
            return false;
        } else {
            return true;
        }
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected
        AbortableIterator<Quintuple<AST_TransformationHeuristic, YNMImplication, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Triple<Position, Set<ProbabilisticRule>, ProbabilisticRule>>>
        getTransformedRules(final Node<ProbabilisticRule> origNode,
            final Graph<ProbabilisticRule, ?> gr,
            final ADP_AST_Problem qdp,
            final Abortion aborter) throws AbortionException {
        return new ADP_AST_TransformationProcessor.MaybeOneIterator<>(
            getTransformed(origNode, gr, qdp));
    }

    private
        Quintuple<AST_TransformationHeuristic, YNMImplication, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Triple<Position, Set<ProbabilisticRule>, ProbabilisticRule>>
        getTransformed(final Node<ProbabilisticRule> origNode,
            final Graph<ProbabilisticRule, ?> gr,
            final ADP_AST_Problem posQDT) throws AbortionException {
        final Set<ProbabilisticRule> newDTs = new LinkedHashSet<>();
        final Set<Pair<ProbabilisticRule, ProbabilisticRule>> resDTs = new LinkedHashSet<>();
        final Set<Pair<ProbabilisticRule, ProbabilisticRule>> resRules = new LinkedHashSet<>();
        final TRSFunctionApplication ellSharp = origNode.getObject().getLhsInStandardRepresentation();
        final MultiDistribution<TRSTerm> distRHS = origNode.getObject().getRhsInStandardRepresentation();

        if (this.initialADPs) { /**BASIC**/
            System.out.println("Basic");
        } else { /**ALL**/
        }

        for (final Node<ProbabilisticRule> u_to_v : gr.getIn(origNode)) {
            final Set<TRSSubstitution> allMGUs;
            if (this.initialADPs) { /**BASIC**/
                allMGUs = posQDT.getReachDependencyGraph()
                    .getConnectingSubstitutions(u_to_v, origNode);
            } else { /**ALL**/
                allMGUs = posQDT.getDependencyGraph()
                    .getConnectingSubstitutions(u_to_v, origNode);
            }

            for (final TRSSubstitution mgu : allMGUs) {
                if (Globals.useAssertions) {
                    // Added by cotto, Term.applySubstitution does not want
                    // sigma==null
                    assert (mgu != null) : "Offending nodes where no connecting substitution was found:\nFrom: "
                        + u_to_v
                        + "\nTo: "
                        + origNode
                        + "\nAST_ADP Problem:\n\n"
                        + posQDT.toString();
                }

                //Generate new lhs
                final TRSFunctionApplication ellSharpSigma = ellSharp.applySubstitution(mgu);

                //Generate new Dist rhs for ADP
                final HashMultiSet<Pair<TRSTerm, BigFraction>> resProbabilityMapForRule = new HashMultiSet<>();
                for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : distRHS.getProbabilityMapping().entrySet()) {
                    final TRSTerm term = entry.getKey().getKey();
                    final BigFraction prob = entry.getKey().getValue();
                    final Integer amount = entry.getValue();

                    // Create termSigma
                    final TRSTerm termSigma = term.applySubstitution(mgu);

                    resProbabilityMapForRule.add(new Pair<>(termSigma, prob), amount);
                }
                final MultiDistribution<TRSTerm> distSigmaForDT = new MultiDistribution<>(resProbabilityMapForRule);

                final ProbabilisticRule generatedDT = ProbabilisticRule.create(ellSharpSigma, distSigmaForDT);
                final ProbabilisticRule newDT = posQDT.getDT(generatedDT);
                newDTs.add(newDT);
                resDTs.add(new Pair<>(generatedDT, newDT));

                final ProbabilisticRule generatedRule = generatedDT.removeAnnos(posQDT.getDeAnnoMap());
                final ProbabilisticRule newRule = posQDT.getRule(generatedRule);
                resRules.add(new Pair<>(generatedRule, newRule));
            }

        }

        if (newDTs.contains(origNode.getObject())) {
            // we have the original DT again, hence ignore this transformation
            return null;
        }

        final AST_TransformationHeuristic heuristic = new InstantiationVariableHeuristic(ellSharp, newDTs);

        // complete for iAST, but for AST only if the instantiated ADP is linear
        final boolean complete = !posQDT.isBasic()
            && (posQDT.isInnermost() || origNode.getObject().isLinear());
        return new Quintuple<>(heuristic,
            complete ? YNMImplication.EQUIVALENT : YNMImplication.SOUND,
            resDTs,
            resRules,
            null);
    }

    static class InstantiationVariableHeuristic implements AST_TransformationHeuristic {

        private final TRSFunctionApplication s;
        private final Set<ProbabilisticRule> newDTs;

        public InstantiationVariableHeuristic(final TRSFunctionApplication s, final Set<ProbabilisticRule> newRules) {
            this.newDTs = newRules;
            this.s = s;
        }

        @Override
        public boolean safeTransformation() {
            // check whether all new pairs contains strictly less variables than the original pair.
            final int nrVars = this.s.getVariables().size();
            for (final ProbabilisticRule rule : this.newDTs) {
                if (rule.getVariables().size() >= nrVars) {
                    return false;
                }
            }
            return true;
        }

    }

}
