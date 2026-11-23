package aprove.verification.probabilistic.Complexity.ADPProblem.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.Graph.Node;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Complexity.ADPProblem.*;
import aprove.verification.probabilistic.Termination.ADPProblem.AST.*;
import aprove.xml.*;

/**
 * General skeleton of a AST_ADP transformation processor.
 *
 * @author J-C Kassing
 * @version $Id$
 */
public abstract class ADP_Cpx_TransformationProcessor extends ADP_Cpx_ProblemProcessor {

    private final ADP_Cpx_Transformation transformation;
    private final int limit;

    public ADP_Cpx_TransformationProcessor(final ADP_Cpx_Transformation transformation,
        final Arguments arguments) {
        this.transformation = transformation;
        this.limit = arguments.limit;
    }

    @Override
    public boolean isCpxADP_Applicable(final ADP_Cpx_Problem posQDT) {
        return posQDT.QsupersetOfLhsS();
    }

    @Override
    protected Result processCpxADPProblem(final ADP_Cpx_Problem posQDT, final Abortion aborter) throws AbortionException {
        final ProbComplexityDependencyGraph graph = posQDT.getDependencyGraph();
        final Graph<ProbabilisticRule, ?> gr = graph.getGraph();

        final ADP_Cpx_TransformationInfo transInfo = graph.getTransformationInfo();
        transInfo.getNrOfOrigins();
        posQDT.getP().size();

        for (final Node<ProbabilisticRule> origNode : gr.getNodes()) {
            final AbortableIterator<Quintuple<CpxADP_TransformationHeuristic, ComplexityImplication, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Triple<Position, Set<ProbabilisticRule>, ProbabilisticRule>>> resultIter =
                getTransformedRules(origNode, gr, posQDT, aborter);
            nextExample: while (resultIter.hasNext(aborter)) {
                final Quintuple<CpxADP_TransformationHeuristic, ComplexityImplication, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Triple<Position, Set<ProbabilisticRule>, ProbabilisticRule>> result =
                    resultIter.next(aborter);

                // Okay, we are successful, let us replace origNode by the new DTs and add the new rules

                final Set<Pair<ProbabilisticRule, ProbabilisticRule>> newDTs = result.x;
                final Set<Pair<ProbabilisticRule, ProbabilisticRule>> newRules = result.y;
                final Triple<Position, Set<ProbabilisticRule>, ProbabilisticRule> triple = result.z;
                Position p;
                Set<ProbabilisticRule> usable;
                ProbabilisticRule rewriteRule;
                if (triple == null) {
                    p = null;
                    usable = null;
                    rewriteRule = null;
                } else {
                    p = triple.x;
                    usable = triple.y;
                    rewriteRule = triple.z;
                }

                final Set<ProbabilisticRule> onlyResultingDTs = new LinkedHashSet<>();
                for (final Pair<ProbabilisticRule, ProbabilisticRule> pair : newDTs) {
                    onlyResultingDTs.add(pair.y);
                }

                final Set<ProbabilisticRule> onlyResultingRules = new LinkedHashSet<>();
                if (posQDT.getSWithQ().contains(origNode.getObject().removeAnnos(posQDT.getDeAnnoMap()))) {
                    for (final Pair<ProbabilisticRule, ProbabilisticRule> pair : newRules) {
                        onlyResultingRules.add(pair.y);
                    }
                }

                final Pair<ADP_Cpx_Problem, Integer> newQdpCounter =
                    posQDT.getTransformedProblem(this.transformation, origNode, onlyResultingDTs, onlyResultingRules, p);
                final ADP_Cpx_Problem newQdp = newQdpCounter.x;

                // let us check heuristics
                final int count = newQdpCounter.y;

                // first check nr of transformations allowed for for this dp
                if (count > this.limit) {
                    aborter.checkAbortion();
                    continue nextExample;
                }

                final Proof proof = new CpxADP_TransformationProof(origNode.getObject(),
                    this.transformation,
                    onlyResultingDTs,
                    onlyResultingRules,
                    p);

                return ResultFactory.proved(newQdp, result.w, proof);
            }
        }

        return ResultFactory.unsuccessful();
    }

    /**
     * the CpxADP_TransformationHeuristic can be returned optional to make some additional transformations safe.
     * @param s_to_t
     * @param gr
     * @param qdp
     * @param aborter
     * @return
     * @throws AbortionException
     */
    protected abstract
        AbortableIterator<Quintuple<CpxADP_TransformationHeuristic, ComplexityImplication, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Triple<Position, Set<ProbabilisticRule>, ProbabilisticRule>>>
        getTransformedRules(Node<ProbabilisticRule> origNode,
            Graph<ProbabilisticRule, ?> gr,
            ADP_Cpx_Problem qdp,
            Abortion aborter) throws AbortionException;

    /**
     * the CpxADP_TransformationHeuristic can be used to make some additional transformations safe.
     */
    static interface CpxADP_TransformationHeuristic {

        public boolean safeTransformation();

    }

    /**
     * an iterator that one time delivers the given element, if
     * this is not null. For null nothing is returned.
     *
     * @author thiemann & Jan-Christoph Kassing
     */
    static class MaybeOneIterator<U> implements AbortableIterator<U> {

        private U element;

        public MaybeOneIterator(final U element) {
            this.element = element;
        }

        @Override
        public boolean hasNext(final Abortion aborter) {
            return this.element != null;
        }

        @Override
        public U next(final Abortion aborter) {
            if (this.element != null) {
                final U e = this.element;
                this.element = null;
                return e;
            } else {
                throw new NoSuchElementException();
            }
        }

    }

    public static final AbortableIterator<Quintuple<CpxADP_TransformationHeuristic, ComplexityImplication, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Triple<Position, Set<ProbabilisticRule>, ProbabilisticRule>>> EMPTY_ITERATOR =
        new MaybeOneIterator<>(
            null);

    static class CpxADP_TransformationProof extends ADP_AST_Proof {

        private final ProbabilisticRule s_to_t;
        /**
         * This set contains pairs, where the first element is the generated rule and the second element is a
         * possibly renamed variant that already existed in the QDP.
         */
        private final Set<ProbabilisticRule> newDTs;
        private final Set<ProbabilisticRule> newRules;
        private final ADP_Cpx_Transformation transformation;
        private final Position position;

        private CpxADP_TransformationProof(final ProbabilisticRule probCoupledPosDepTuple,
            final ADP_Cpx_Transformation transformation,
            final Set<ProbabilisticRule> newDTs,
            final Set<ProbabilisticRule> newRules,
            final Position position) {

            this.s_to_t = probCoupledPosDepTuple;
            this.newDTs = newDTs;
            this.newRules = newRules;
            this.transformation = transformation;
            this.position = position;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuffer s = new StringBuffer();
            s.append(o.export("By " + this.transformation.getPredicate() + " " + o.cite(this.transformation.getCitation()) + " for the rule ") + o.math(o.export(this.s_to_t))
                +
                (this.position == null ? "" : " at position " + o.export(this.position))
                + " we obtained the following new ADPs :");
            s.append(o.cond_linebreak());
            s.append(o.set(this.newDTs, Export_Util.RULES));
            s.append(o.cond_linebreak());
            s.append(o.export("and we added the following new probabilistic rules with active return value flag:"));
            s.append(o.cond_linebreak());
            s.append(o.set(this.newRules, Export_Util.RULES));
            return s.toString();
        }

        @Override
        public Element toCPF(final Document doc, final Element[] childrenProofs, final XMLMetaData xmlMetaData, final CPFModus modus) {
            return null;
        }

        @Override
        public boolean isCPFCheckableProof(final CPFModus modus) {
            return false;
        }

    }

    /**
     * For use with our children and annotation @ParamsViaArgumentObjects
     */
    public static class Arguments {

        public int limit = 0;
    }

}
