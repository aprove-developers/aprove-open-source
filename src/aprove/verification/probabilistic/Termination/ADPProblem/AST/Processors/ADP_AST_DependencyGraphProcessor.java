package aprove.verification.probabilistic.Termination.ADPProblem.AST.Processors;

import java.util.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.ADPProblem.*;
import aprove.verification.probabilistic.Termination.ADPProblem.AST.*;

/**
 * Dependency Graph Processor as described in Kassing's master's thesis, CADE23, and FLOPS24 for ADPs
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class ADP_AST_DependencyGraphProcessor extends ADP_AST_ProblemProcessor {

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isAST_ADPApplicable(final ADP_AST_Problem qdp) {
        final ProbQDependencyGraph graph = qdp.getDependencyGraph();
        return !graph.isSCC();
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processAST_ADPProblem(final ADP_AST_Problem origpqdp, final Abortion aborter) throws AbortionException {

        final ProbQDependencyGraph graph = origpqdp.getDependencyGraph();

        final List<ADP_AST_Problem> resultObls = new ArrayList<>();

        final Set<Cycle<ProbabilisticRule>> sccs = graph.getGraph().getSCCs(false);
        if (graph.isSCC()) {
            // Since we already know from the applicability check that isGenuineSCC = false,
            // this means that we have a singleton node (should only occur in certain
            // certification modes).
            return ResultFactory.proved(origpqdp,
                YNMImplication.EQUIVALENT,
                new AST_ADPDependencyGraphProof(graph, 0, 0, origpqdp.isInnermost(), origpqdp.isBasic()));
        }

        graph.getGraph();
        final Iterable<Cycle<ProbabilisticRule>> maybeRankedSccGraph;
        int iteratorSize = 0;

        maybeRankedSccGraph = sccs;
        iteratorSize = sccs.size();

        //        No Certification, yet.
        //        if (Options.certifier.isCpf()) {
        //            // ugly hack
        //            final SCCGraph<ProbabilisticRule, ?> sccGraph = new SCCGraph<>(sccs, g);
        //            maybeRankedSccGraph = sccGraph.getRankedSCCs();
        //            iteratorSize = ((List<?>) maybeRankedSccGraph).size();
        //        } else {
        //            maybeRankedSccGraph = sccs;
        //            iteratorSize = sccs.size();
        //        }

        final Set<ADP_AST_Problem> newProblems = new LinkedHashSet<>();
        int size = 0;

        final LinkedList<Integer> nonSccs = new LinkedList<>();
        int iterator = 0;
        for (final Cycle<ProbabilisticRule> rankedScc : maybeRankedSccGraph) {
            iterator++;
            final ProbQDependencyGraph subScc = graph.getSubGraph(rankedScc);
            if (subScc.isGenuineSCC()) {
                final ADP_AST_Problem newProblem;
                if (origpqdp.isBasic()) { /**Basic**/
                    newProblem = origpqdp.getSubProblemWithReachability(subScc);
                } else { /**Full and Innermost**/
                    newProblem = origpqdp.getSubProblem(subScc);
                }
                newProblems.add(newProblem);
                resultObls.add(newProblem);
                size += newProblem.getP().size();
            } else {
                nonSccs.add(iteratorSize - iterator + 1);
            }
        }
        final int lessNodes = origpqdp.getP().size() - size;
        final int nrSccs = newProblems.size();

        final AST_ADPDependencyGraphProof DGPproof =
            new AST_ADPDependencyGraphProof(graph, nrSccs, lessNodes, origpqdp.isInnermost(), origpqdp.isBasic());

        final Result result = ResultFactory.provedAnd(newProblems, YNMImplication.EQUIVALENT, DGPproof);
        return result;

    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class AST_ADPDependencyGraphProof extends ADP_AST_Proof implements DOT_Able {

        private final ProbQDependencyGraph graph;
        private final int nrSccs;
        private final int lessNodes;
        private final boolean innermost;
        private final boolean basic;

        private AST_ADPDependencyGraphProof(final ProbQDependencyGraph graph,
            final int nrSccs,
            final int lessNodes,
            final boolean innermost,
            final boolean basic) {
            this.graph = graph;
            this.nrSccs = nrSccs;
            this.lessNodes = lessNodes;
            this.innermost = innermost;
            this.basic = basic;
        }

        private static final Citation[] citations = new Citation[] { Citation.LPAR04,
            Citation.FROCOS05,
            Citation.EDGSTAR };

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder res = new StringBuilder();
            res.append(o.paragraph());
            if (!this.basic) { //innermost and full AST
                res.append("We use the dependency graph processor ").append(o.cite(Citation.KASSING_DISS)).append(".");
            } else { //basic AST
                res.append("We use the dependency graph processor ").append(o.cite(Citation.JPK60)).append(".");
            }
            res.append(o.linebreak());
            res.append("The approximation of the Dependency Graph ")
                .append(o.cite(AST_ADPDependencyGraphProof.citations))
                .append(" contains ")
                .append(this.nrSccs)
                .append(" SCC")
                .append(this.nrSccs == 1 ? "" : "s");
            if (this.lessNodes > 0) {
                res.append(" with ").append(this.lessNodes).append(" less node").append(this.lessNodes == 1 ? "" : "s").append(".");
            } else {
                res.append(".");
            }

            return o.export(res.toString());
        }

        @Override
        public String toDOT() {
            return this.graph.toDOT();
        }

    }

}
