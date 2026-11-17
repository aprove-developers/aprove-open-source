package aprove.verification.probabilistic.Termination.ADPProblem.AST.Processors;

import java.util.*;

import org.w3c.dom.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.oldframework.Utility.Graph.Node;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.ADPProblem.*;
import aprove.verification.probabilistic.Termination.ADPProblem.AST.*;
import aprove.xml.*;

/**
 * General skeleton of a AST_ADP transformation processor.
 *
 * @author J-C Kassing
 * @version $Id$
 */
public abstract class ADP_AST_TransformationProcessor extends ADP_AST_ProblemProcessor {

    private final ADP_AST_Transformation transformation;
    private final int limit;
    // True if we consider only basic problems and
    protected final boolean initialADPs;

    public ADP_AST_TransformationProcessor(final ADP_AST_Transformation transformation,
        final Arguments arguments) {
        this.transformation = transformation;
        this.limit = arguments.limit;
        this.initialADPs = arguments.initialADPs;
    }

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isAST_ADPApplicable(final ADP_AST_Problem posQDT) {
        if (posQDT.isBasic()) { /**BASIC**/
            // not for bAST: the transformations also replace the ADP in the reachability component,
            // which loses the steps from basic start terms (and from predecessors/successors outside of P)
            return false;
        } /**FULL and INNERMOST**/
        return posQDT.getDependencyGraph().isSCC() && !this.initialADPs;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processAST_ADPProblem(final ADP_AST_Problem posQDT, final Abortion aborter) throws AbortionException {

        final ProbQDependencyGraph graph;
        final Graph<ProbabilisticRule, ?> gr;

        final ADP_AST_TransformationInfo transInfo;
        final int originSize;
        final int Psize;

        if (this.initialADPs) { /**BASIC**/
            graph = posQDT.getReachDependencyGraph();
        } else { /**FULL, INNERMOST and BASIC**/
            graph = posQDT.getDependencyGraph();
        }
        gr = graph.getGraph();

        transInfo = graph.getTransformationInfo();
        originSize = transInfo.getNrOfOrigins();
        Psize = posQDT.getP().size();

        for (final Node<ProbabilisticRule> origNode : gr.getNodes()) {
            if (this.initialADPs && posQDT.getP().contains(origNode.getObject())) { /**BASIC**/
                continue; //We only want to consider initial ADPs
            }
            final AbortableIterator<Quintuple<AST_TransformationHeuristic, YNMImplication, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Triple<Position, Set<ProbabilisticRule>, ProbabilisticRule>>> resultIter =
                getTransformedRules(origNode, gr, posQDT, aborter);
            nextExample: while (resultIter.hasNext(aborter)) {
                final Quintuple<AST_TransformationHeuristic, YNMImplication, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Triple<Position, Set<ProbabilisticRule>, ProbabilisticRule>> result =
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
                if (posQDT.getS().contains(origNode.getObject().removeAnnos(posQDT.getDeAnnoMap()))) {
                    for (final Pair<ProbabilisticRule, ProbabilisticRule> pair : newRules) {
                        onlyResultingRules.add(pair.y);
                    }
                }

                final Pair<ADP_AST_Problem, Integer> newQdpCounter =
                    posQDT.getTransformedProblem(this.transformation, origNode, onlyResultingDTs, onlyResultingRules, p);
                final ADP_AST_Problem newQdp = newQdpCounter.x;

                // let us check heuristics
                final int count = newQdpCounter.y;

                // first check nr of transformations allowed for for this dp
                if (count > this.limit) {
                    // if this is not yet safe, try size criterion
                    final ProbQDependencyGraph newGraph = newQdp.getDependencyGraph();
                    final Set<Node<ProbabilisticRule>> newSccNodes = newGraph.getNodesOnSCCs();
                    if (newSccNodes.size() >= Psize) {
                        // and check origin criterion
                        ADP_AST_TransformationInfo newTransformation = newGraph.getTransformationInfo();
                        newTransformation = newTransformation.getSubInfo(newSccNodes);
                        if (originSize == newTransformation.getNrOfOrigins()) {
                            // and finally check transformation specific criterion
                            if (result.v == null || !result.v.safeTransformation()) {
                                aborter.checkAbortion();
                                continue nextExample;
                            }
                        }
                    }
                }

                final Proof proof = new AST_ADPTransformationProof(origNode.getObject(),
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
     * the AST_TransformationHeuristic can be returned optional to make some additional transformations safe.
     * @param s_to_t
     * @param gr
     * @param qdp
     * @param aborter
     * @return
     * @throws AbortionException
     */
    protected abstract
        AbortableIterator<Quintuple<AST_TransformationHeuristic, YNMImplication, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Triple<Position, Set<ProbabilisticRule>, ProbabilisticRule>>>
        getTransformedRules(Node<ProbabilisticRule> origNode,
            Graph<ProbabilisticRule, ?> gr,
            ADP_AST_Problem qdp,
            Abortion aborter) throws AbortionException;

    /**
     * the AST_TransformationHeuristic can be used to make some additional transformations safe.
     */
    static interface AST_TransformationHeuristic {

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

    public static final AbortableIterator<Quintuple<AST_TransformationHeuristic, YNMImplication, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Set<Pair<ProbabilisticRule, ProbabilisticRule>>, Triple<Position, Set<ProbabilisticRule>, ProbabilisticRule>>> EMPTY_ITERATOR =
        new MaybeOneIterator<>(
            null);

    static class AST_ADPTransformationProof extends ADP_AST_Proof {

        private final ProbabilisticRule s_to_t;
        /**
         * This set contains pairs, where the first element is the generated rule and the second element is a
         * possibly renamed variant that already existed in the QDP.
         */
        private final Set<ProbabilisticRule> newDTs;
        private final Set<ProbabilisticRule> newRules;
        private final ADP_AST_Transformation transformation;
        private final Position position;

        private AST_ADPTransformationProof(final ProbabilisticRule probCoupledPosDepTuple,
            final ADP_AST_Transformation transformation,
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
            s.append(o.export("By " + this.transformation.getPredicate() + " " + o.cite(this.transformation.getCitation()) + " for the rule ")
                + o.math(o.export(this.s_to_t))
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
        public boolean initialADPs = false;
    }

}
