package aprove.verification.probabilistic.Termination.ADPProblem.AST.Processors;

import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.ADPProblem.*;
import aprove.verification.probabilistic.Termination.ADPProblem.AST.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import immutables.*;

/**
 * The forward instantiation processor for ADPs as described in FLOPS24
 *
 * @author J-C Kassing
 */
public class ADP_AST_RewritingProcessor extends ADP_AST_TransformationProcessor {

    @ParamsViaArgumentObject
    public ADP_AST_RewritingProcessor(final Arguments arguments) {
        super(ADP_AST_Transformation.Rewriting, arguments);
    }

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isAST_ADPApplicable(final ADP_AST_Problem ast_ADP) {
        if (!ast_ADP.isInnermost()) { /**FULL and BASIC**/
            return false;
        } else { /**INNERMOST**/
            // does not work for parallel-simultaneous rewriting (yet)
            if (ast_ADP.getStrat() == QRewriteStrategy.Q_PARALLEL_SIMULTANEOUS) {
                return false;
            }
            // demand graph-reduces and R = U(P,R)
            final int n = ast_ADP.getUsableRules().size();
            return super.isAST_ADPApplicable(ast_ADP) && n > 0 && n == ast_ADP.getS().size();
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
            final ADP_AST_Problem ast_posqdt,
            final Abortion aborter) throws AbortionException {
        return new ADP_AST_TransformationProcessor.MaybeOneIterator<>(
            getTransformed(origNode, ast_posqdt, aborter));
    }

    private
        Quintuple<AST_TransformationHeuristic, YNMImplication, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Triple<Position, Set<ProbabilisticRule>, ProbabilisticRule>>
        getTransformed(final Node<ProbabilisticRule> oldDTNode,
            final ADP_AST_Problem ast_posqdt,
            final Abortion aborter) throws AbortionException {
        final Set<ProbabilisticRule> newDTs = new LinkedHashSet<>();
        final Set<Pair<ProbabilisticRule, ProbabilisticRule>> resDTs = new LinkedHashSet<>();
        final Set<ProbabilisticRule> newRules = new LinkedHashSet<>();
        final Set<Pair<ProbabilisticRule, ProbabilisticRule>> resRules = new LinkedHashSet<>();

        final PQTRSProblem qtrs = ast_posqdt.getSwithQ();
        final boolean nonOverlapping = qtrs.getCriticalPairs().isNonOverlapping(aborter);

        // determine redexes // perhaps cache these results

        final Map<FunctionSymbol, ImmutableSet<ProbabilisticRule>> ruleMap = qtrs.getRuleMap();

        final ProbabilisticRule oldDT = oldDTNode.getObject();
        final TRSFunctionApplication s = oldDT.getLeft();
        final MultiDistribution<TRSTerm> rhsDistOldDT = oldDT.getRight();
        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rhsDistOldDT.getProbabilityMapping().entrySet()) {
            final TRSTerm origTerm = entry.getKey().getKey();
            final BigFraction prob = entry.getKey().getValue();

            for (final Pair<TRSFunctionApplication, Position> positionalSubterm : origTerm
                .getAnnoSubtermsWithPositions(ast_posqdt.getDeAnnoMap())) {

                subterms: for (final Pair<Position, TRSTerm> posWithSub : positionalSubterm.x.getPositionsWithSubTerms()) {

                    // Check whether there is no annotated subterm with a position below
                    // the position pi(positionalSubterm).pi(posWithSub) or equal to it.
                    // Otherwise, the processor is not applicable on this position subterm
                    if (origTerm.getSubterm(positionalSubterm.y.append(posWithSub.x)).countAnnos(ast_posqdt.getDeAnnoMap().keySet()) > 0) {
                        continue subterms;
                    }

                    final TRSTerm subTerm = posWithSub.y;
                    if (!subTerm.isVariable()) {
                        final TRSFunctionApplication sub = (TRSFunctionApplication) subTerm;
                        final Set<ProbabilisticRule> possibleRules = ruleMap.get(sub.getRootSymbol());
                        if (possibleRules != null) {
                            for (final ProbabilisticRule rule : possibleRules) {
                                final TRSSubstitution matcher = rule.getLeft().getMatcher(subTerm);
                                if (matcher != null) {
                                    // okay, we can rewrite
                                    final Set<ProbabilisticRule> localUsableRules = ProbQUsableRules.getUsableRulesOfTerm(subTerm, ruleMap, ast_posqdt.getDeAnnoMap());
                                    final PQTRSProblem localSubPQTRS = qtrs.createSubProblem(ImmutableCreator.create(localUsableRules));
                                    // let us check non-overlappingness
                                    if (nonOverlapping) {
                                        // we get NO for free
                                    } else {
                                        // we have to check for NO of the locally usable rules
                                        if (!localSubPQTRS.getCriticalPairs().isNonOverlapping(aborter)) {
                                            continue subterms;
                                        }
                                    }

                                    // Next, we have to check, whether L and NE is satisfied for the used rewrite rule
                                    if (rule.isLinear() && !rule.isVariableOccDecreasing()) {
                                        // L and VOND (which is equal to NE if L is true) is satisfied
                                    } else {
                                        // or all rules are non-probabilistic
                                        if (localSubPQTRS.isNonProbabilistic()) {
                                            // all rules are non-probabilistic is satisfied
                                        } else {
                                            // or the rewrite step is an innermost rewrite step without variables below
                                            final Set<TRSTerm> allProperSubterms = subTerm.getSubTerms();
                                            allProperSubterms.remove(subTerm);
                                            if (subTerm.getVariables().isEmpty() && !qtrs.getQ().someTermCanBeRewritten(allProperSubterms)) {
                                                // innermost rewrite step without variables below is satisfied
                                            } else {
                                                // non of our cases are applicable for this subterm, search for the next one
                                                continue subterms;
                                            }
                                        }
                                    }

                                    //As one of our cases for the processor holds, apply the rewrite step now.
                                    final Position p = positionalSubterm.y.append(posWithSub.x);
                                    final MultiDistribution<TRSTerm> rewrittenTermDist = origTerm.rewrite(rule, p, matcher);

                                    //and exchange the old pair in the rhsDist with the multiple new ones (with certain probability)
                                    final HashMultiSet<Pair<TRSTerm, BigFraction>> rhsDistProbMapping = new HashMultiSet<>();
                                    rhsDistProbMapping.addAll(rhsDistOldDT.getProbabilityMapping());
                                    for (final Entry<Pair<TRSTerm, BigFraction>, Integer> newEntry : rewrittenTermDist.getProbabilityMapping().entrySet()) {
                                        final Integer newEntryAmount = newEntry.getValue();
                                        final Pair<TRSTerm, BigFraction> newEntryPair = newEntry.getKey();

                                        final BigFraction newProbability = newEntryPair.y.multiply(prob);
                                        for (int i = 0; i < newEntryAmount; i++) {
                                            rhsDistProbMapping.add(new Pair<>(newEntry.getKey().getKey(), newProbability));
                                        }
                                    }
                                    rhsDistProbMapping.removeOne(entry.getKey());

                                    final MultiDistribution<TRSTerm> newRHS = MultiDistribution.create(rhsDistProbMapping);
                                    final ProbabilisticRule generatedNewDT = ProbabilisticRule.create(oldDT.getLeft(), newRHS);
                                    final ProbabilisticRule newDT = ast_posqdt.getDT(generatedNewDT);
                                    newDTs.add(newDT);
                                    resDTs.add(new Pair<>(generatedNewDT, newDT));

                                    final ProbabilisticRule generatedNewRule = generatedNewDT.removeAnnos(ast_posqdt.getDeAnnoMap());
                                    final ProbabilisticRule newRule = ast_posqdt.getRule(generatedNewDT.removeAnnos(ast_posqdt.getDeAnnoMap()));
                                    newRules.add(newRule);
                                    resRules.add(new Pair<>(generatedNewRule, newRule));

                                    final Triple<Position, Set<ProbabilisticRule>, ProbabilisticRule> triple = new Triple<>(p, localUsableRules, rule);

                                    final AST_TransformationHeuristic heuristic = new RewritingHeuristic();

                                    return new Quintuple<>(heuristic, YNMImplication.SOUND, resDTs, resRules, triple);
                                }
                            }
                        }
                    }
                }
            }
        }
        return null;
    }

    static class RewritingHeuristic implements AST_TransformationHeuristic {

        @Override
        public boolean safeTransformation() {
            return false;
        }

    }
}
