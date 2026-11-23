package aprove.verification.probabilistic.Complexity.ADPProblem.Processors;

import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;

import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Complexity.ADPProblem.*;

/**
 * The rule overlap instantiation processor for ADPs as described in FLOPS24
 *
 * @author J-C Kassing
 */
public class ADP_Cpx_RuleOverlapInstProcessor extends ADP_Cpx_TransformationProcessor {

    @ParamsViaArgumentObject
    public ADP_Cpx_RuleOverlapInstProcessor(final Arguments arguments) {
        super(ADP_Cpx_Transformation.RuleOverlapInstantiation, arguments);
    }

    @Override
    protected
        AbortableIterator<Quintuple<CpxADP_TransformationHeuristic, ComplexityImplication, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Triple<Position, Set<ProbabilisticRule>, ProbabilisticRule>>>
        getTransformedRules(final Node<ProbabilisticRule> origNode,
            final Graph<ProbabilisticRule, ?> gr,
            final ADP_Cpx_Problem qdp,
            final Abortion aborter) throws AbortionException {
        return new ADP_Cpx_TransformationProcessor.MaybeOneIterator<>(
            getTransformed(origNode,
                qdp));

    }

    private
        Quintuple<CpxADP_TransformationHeuristic, ComplexityImplication, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Triple<Position, Set<ProbabilisticRule>, ProbabilisticRule>>
        getTransformed(final Node<ProbabilisticRule> origNode,
            final ADP_Cpx_Problem posQDT) throws AbortionException {
        final Set<ProbabilisticRule> newDTs = new LinkedHashSet<>();
        final Set<Pair<ProbabilisticRule, ProbabilisticRule>> resDTs = new LinkedHashSet<>();
        final Set<Pair<ProbabilisticRule, ProbabilisticRule>> resRules = new LinkedHashSet<>();
        final TRSFunctionApplication ellSharp = origNode.getObject().getLhsInStandardRepresentation();
        final MultiDistribution<TRSTerm> distRHS = origNode.getObject().getRhsInStandardRepresentation();

        // go through the rhs and try to narrow at some point.
        final Map<Pair<TRSFunctionApplication, Position>, List<NarrowingPos>> fullNarrowingsMap = new HashMap<>();

        for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : distRHS.getProbabilityMapping().entrySet()) {
            final TRSTerm term = entry.getKey().getKey();

            for (final Pair<TRSFunctionApplication, Position> pair : term.getAnnoSubtermsWithPositions(posQDT.getDeAnnoMap())) {

                final List<NarrowingPos> narrowsForTerm = new ArrayList<>();
                narrowsForTerm.addAll(getNarrowablesRoot(pair, ellSharp, posQDT.getP(), posQDT.getSwithQ().getPR()));
                narrowsForTerm.addAll(getNarrowablesBelowRoot(pair, ellSharp, posQDT.getSwithQ().getPR()));
                fullNarrowingsMap.put(pair, narrowsForTerm);

            }

        }

        // take an arbitrary positional subterm that we can instantiate
        Pair<TRSFunctionApplication, Position> target = null;
        for (final Entry<Pair<TRSFunctionApplication, Position>, List<NarrowingPos>> entry : fullNarrowingsMap.entrySet()) {
            final Pair<TRSFunctionApplication, Position> posSubterm = entry.getKey();
            final List<NarrowingPos> narrowsForPosSubterm = entry.getValue();

            // check whether we possibly result with the same DT after ROIing this position subterm.
            boolean canBeROIed = true;
            for (final NarrowingPos narrow : narrowsForPosSubterm) {
                if (posSubterm.x.applySubstitution(narrow.mgu).equals(posSubterm.x)) {
                    canBeROIed = false; // we get the same DT so do not use this term for ROI
                }
            }
            if (canBeROIed) {
                target = posSubterm;
                break;
            }
        }

        // check if we can narrow some position subterm
        if (target == null) {
            return null;
        }

        final List<NarrowingPos> narrowListForTarget = fullNarrowingsMap.get(target);

        // find positional subterms that are not captured by the narrowing substitutions of posSubtermToNarrow
        final Set<Pair<TRSFunctionApplication, Position>> setOfNotCaptured = new HashSet<>();
        for (final Entry<Pair<TRSFunctionApplication, Position>, List<NarrowingPos>> entry : fullNarrowingsMap.entrySet()) {
            final Pair<TRSFunctionApplication, Position> posSubterm = entry.getKey();
            final List<NarrowingPos> narrowListForPosSubterm = entry.getValue();

            // check whether for all the narrow substitutions we can find one for posSubtermToNarrow that is more general on the term,
            // i.e., for every narrow sub tau from posSubterm we can find a narrow sub pi from target
            // such that posSubterm.pi matches posSubterm.tau
            for (final NarrowingPos narrowForPosSubterm : narrowListForPosSubterm) {
                final TRSSubstitution tau = narrowForPosSubterm.mgu;

                boolean isCaptured = false;
                for (final NarrowingPos narrowForTarget : narrowListForTarget) {
                    final TRSSubstitution pi = narrowForTarget.mgu;
                    // covered: pi is more general than tau, i.e., tau = pi rho for some rho
                    if (tau.isInstanceOf(pi)) {
                        isCaptured = true;
                    }
                }
                if (!isCaptured) {
                    setOfNotCaptured.add(posSubterm);
                }
            }
        }

        // finally, create the new DTs

        // first the ones by applying the narrowing substitution
        for (final NarrowingPos narrowForTarget : narrowListForTarget) {
            final TRSSubstitution mgu = narrowForTarget.mgu;

            //Generate new lhs
            final TRSFunctionApplication ellSharpSigma = ellSharp.applySubstitution(mgu);

            //Generate new Dist rhs for both DT and the new rule
            final HashMultiSet<Pair<TRSTerm, BigFraction>> resProbabilityMapForRule = new HashMultiSet<>();
            for (final Entry<Pair<TRSTerm, BigFraction>, Integer> distEntry : distRHS.getProbabilityMapping().entrySet()) {
                final TRSTerm term = distEntry.getKey().getKey();
                final BigFraction prob = distEntry.getKey().getValue();
                final Integer amount = distEntry.getValue();

                // Create termSigma
                final TRSTerm termSigma = term.applySubstitution(mgu);

                resProbabilityMapForRule.add(new Pair<>(termSigma, prob), amount);
            }
            final MultiDistribution<TRSTerm> distSigma = new MultiDistribution<>(resProbabilityMapForRule);

            final ProbabilisticRule generatedDT = ProbabilisticRule.create(ellSharpSigma, distSigma);
            final ProbabilisticRule newDT = posQDT.getDT(generatedDT);
            newDTs.add(newDT);
            resDTs.add(new Pair<>(generatedDT, newDT));

            final ProbabilisticRule generatedRule = generatedDT.removeAnnos(posQDT.getDeAnnoMap());
            final ProbabilisticRule newRule = posQDT.getRule(generatedRule);
            resRules.add(new Pair<>(generatedRule, newRule));
        }
        // and second, the dt for the positional subterms that are not captured
        // if at least one of the positional subterms are not captured

        if (!setOfNotCaptured.isEmpty()) {
            //Generate new Dist rhs for both DT and the new rule
            final HashMultiSet<Pair<TRSTerm, BigFraction>> resProbabilityMapForRule = new HashMultiSet<>();
            for (final Entry<Pair<TRSTerm, BigFraction>, Integer> distEntry : distRHS.getProbabilityMapping().entrySet()) {
                final TRSTerm term = distEntry.getKey().getKey();
                final BigFraction prob = distEntry.getKey().getValue();
                final Integer amount = distEntry.getValue();

                final TRSTerm flatTerm = term.renameAtAllMap(term.getPositions(), posQDT.getDeAnnoMap());

                final Set<Position> setNotCapturedPos = new HashSet<>();
                for (final Pair<TRSFunctionApplication, Position> termPositionPair : term.getAnnoSubtermsWithPositions(posQDT.getDeAnnoMap())) {
                    if (setOfNotCaptured.contains(termPositionPair)) {
                        setNotCapturedPos.add(termPositionPair.y);
                    }
                }

                final TRSTerm newterm = flatTerm.renameAtAllMap(setNotCapturedPos, posQDT.getAnnoMap());

                resProbabilityMapForRule.add(new Pair<>(newterm, prob), amount);
            }
            final MultiDistribution<TRSTerm> distSigma = new MultiDistribution<>(resProbabilityMapForRule);
            final ProbabilisticRule generatedDT = ProbabilisticRule.create(origNode.getObject().getStandardRepresentation().getLeft(), distSigma);
            final ProbabilisticRule newDT = posQDT.getDT(generatedDT);
            newDTs.add(newDT);
            resDTs.add(new Pair<>(generatedDT, newDT));
        }

        if (newDTs.contains(origNode.getObject())) {
            // we have the original DT again, hence ignore this transformation
            return null;
        }

        final CpxADP_TransformationHeuristic heuristic = new InstantiationVariableHeuristic(ellSharp, newDTs);

        return new Quintuple<>(heuristic, UpperBound.create(), resDTs, resRules, null);
    }

    /**
     * Computes all narrowing positions at the root, i.e., mgus with DTs
     * for the given narrowTerm, while keeping lhs in normal form
     * with the narrowing substitutions.
     */
    private List<NarrowingPos>
        getNarrowablesRoot(final Pair<TRSFunctionApplication, Position> toNarrow,
            final TRSTerm lhs,
            final Set<ProbabilisticRule> dtSet,
            final Set<ProbabilisticRule> usableRules) {
        final List<NarrowingPos> narrowables = new ArrayList<>();

        for (final ProbabilisticRule dt : dtSet) {
            final TRSFunctionApplication dtTupleLeft =
                dt.getLeft().renumberVariables(new HashMap<>(), TRSTerm.SECOND_STANDARD_PREFIX, TRSTerm.STANDARD_NUMBER).x;
            final TRSSubstitution mgu = toNarrow.x.getMGU(dtTupleLeft);
            if (mgu != null && lhs.applySubstitution(mgu).isNormal(usableRules) && dtTupleLeft.applySubstitution(mgu).isNormal(usableRules)) {
                narrowables.add(new NarrowingPos(toNarrow, Position.EPSILON, toNarrow.x, dt, mgu));
            }
        }

        return narrowables;
    }

    /**
     * Computes all narrowing positions at the root, i.e., mgus with DTs
     * for the given narrowTerm, while keeping lhs in normal form
     * with the narrowing substitutions.
     */
    private List<NarrowingPos>
        getNarrowablesBelowRoot(final Pair<TRSFunctionApplication, Position> toNarrow, final TRSTerm lhs, final Set<ProbabilisticRule> usableRules) {
        final List<NarrowingPos> narrowables = new ArrayList<>();

        for (final Pair<Position, TRSTerm> pair : toNarrow.x.getPositionsWithSubTerms()) {
            if (pair.x.equals(Position.EPSILON) || pair.y.isVariable()) {
                continue;
            }
            for (final ProbabilisticRule rule : usableRules) {
                final TRSFunctionApplication ruleLeft =
                    rule.getLeft().renumberVariables(new HashMap<>(), TRSTerm.SECOND_STANDARD_PREFIX, TRSTerm.STANDARD_NUMBER).x;
                final TRSSubstitution mgu = pair.y.getMGU(ruleLeft);
                if (mgu != null && lhs.applySubstitution(mgu).isNormal(usableRules)
                    && ruleLeft.applySubstitution(mgu).areAllProperSubtermsInNormal(usableRules)) {
                    narrowables.add(new NarrowingPos(toNarrow, pair.x, (TRSFunctionApplication) pair.y, rule, mgu));
                }
            }
        }

        return narrowables;
    }

    static class NarrowingPos {

        public final Pair<TRSFunctionApplication, Position> posSubterm;
        public final Position pos;
        public final TRSFunctionApplication t;
        public final TRSSubstitution mgu;

        //dt is only non-null if pos = epsilon
        public final ProbabilisticRule dt;

        //rule is only non-null if pos /= epsilon
        public final ProbabilisticRule rule;

        public NarrowingPos(final Pair<TRSFunctionApplication, Position> posSubterm,
            final Position pos,
            final TRSFunctionApplication t,
            final ProbabilisticRule dt,
            final TRSSubstitution mgu) {

            this.posSubterm = posSubterm;
            this.pos = pos;
            this.t = t;
            this.dt = dt;
            this.rule = null;
            this.mgu = mgu;
        }

    }

    static class InstantiationVariableHeuristic implements CpxADP_TransformationHeuristic {

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
