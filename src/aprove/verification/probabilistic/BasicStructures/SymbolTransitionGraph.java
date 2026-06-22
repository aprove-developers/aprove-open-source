package aprove.verification.probabilistic.BasicStructures;

import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.oldframework.Utility.Graph.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import immutables.*;

/**
 * @author J-C Kassing
 * @version $Id$
 */
public class SymbolTransitionGraph implements Immutable {

    // ================================================================================
    // Properties
    // ================================================================================

    private final Graph<FunctionSymbol, ?> g;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    /**
     * create Graph from scratch, if P is given, or start with "graph", if graph is given.
     * @param PTRSProblem - The underlying ptrsproblem
     */
    public SymbolTransitionGraph(Set<ProbabilisticRule> pr, ImmutableSet<FunctionSymbol> signature) {
        this.g = new Graph();

        final Set<FunctionSymbol> fsyms = signature;
        //Nodes
        for (final FunctionSymbol f : fsyms) {
            final Node<FunctionSymbol> newNode = new Node<>(f);
            this.g.addNode(newNode);
        }
        //Edges
        for (final ProbabilisticRule prule : pr) {
            final FunctionSymbol rootLeft = prule.getLeft().getFunctionSymbol();
            for (final Entry<?, Integer> entry : prule.getRight().getProbabilityMapping().entrySet()) {
                final TRSTerm term = ((Pair<TRSTerm, BigFraction>) entry.getKey()).getKey();

                final Node<FunctionSymbol> leftNode = this.g.getNodeFromObject(rootLeft);
                if (term.isVariable()) { // The rule is collapsing so add an edge to all possible Functionsymbols
                    for (final FunctionSymbol f : fsyms) {
                        final Node<FunctionSymbol> rightNode = this.g.getNodeFromObject(f);
                        this.g.addEdge(leftNode, rightNode);
                    }
                } else {
                    for (final FunctionSymbol f : fsyms) {
                        if (term.getFunctionSymbols().contains(f)) {
                            final Node<FunctionSymbol> rightNode = this.g.getNodeFromObject(f);
                            this.g.addEdge(leftNode, rightNode);
                        }
                    }
                }
            }
        }
    }

    public boolean isReachable(final FunctionSymbol from, final FunctionSymbol to) {
        final Node<FunctionSymbol> nodeFrom = this.g.getNodeFromObject(from);
        final Node<FunctionSymbol> nodeTo = this.g.getNodeFromObject(to);
        return this.g.hasPath(nodeFrom, nodeTo);
    }

    // ================================================================================
    // Utility
    // ================================================================================

    public String toDOT() {
        return this.g.toDOT(false);
    }

}
