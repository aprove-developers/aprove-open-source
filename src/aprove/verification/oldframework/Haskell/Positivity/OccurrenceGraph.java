package aprove.verification.oldframework.Haskell.Positivity;

import java.util.*;
import java.util.function.*;

import aprove.verification.oldframework.Haskell.Modules.*;

/**
 * Directed graph whose nodes are type definitions. An edge {@code a -[p]-> b} means that {@code a} occurs
 * in the declaration of {@code b} with polarity {@code p}. A node stands for the declaration itself and
 * does not distinguish the arguments of a type, see {@link GraphBuilder} for how these are handled.
 *
 * Only the edges are stored, since a node without edges does not affect any occurrence.
 *
 * This class is mutable on purpose: it is a builder-style accumulator that {@link GraphBuilder} fills once while walking
 * the declarations and that is only queried afterwards.
 */
public class OccurrenceGraph {

    /** Maps each source node to its targets and the polarity of the respective edge. */
    private final Map<Node, Map<Node, Occurrence>> edges = new LinkedHashMap<>();

    /**
     * Adds an edge to the graph. If there already is an edge between the given nodes, the polarities are
     * combined via {@link Occurrence#oplus(Occurrence)}.
     *
     * @param source the occurring node
     * @param target the node in which source occurs
     * @param occ the polarity of the occurrence
     */
    public void addEdge(final Node source, final Node target, final Occurrence occ) {
        this.edges.computeIfAbsent(source, k -> new LinkedHashMap<>()).merge(target, occ, Occurrence::oplus);
    }

    private Map<Node, Occurrence> outEdges(final Node source) {
        return this.edges.getOrDefault(source, Map.of());
    }

    /**
     * Search state of {@link OccurrenceGraph#transitiveOccurrence(Node, Node)}: The node reached and the
     * polarity of the path that reached it.
     */
    private record PathState(Node node, Occurrence polarity) {
    }

    /**
     * Computes the sum of the polarities of all non-empty paths from source to target which do not visit
     * target in between. In particular, {@code transitiveOccurrence(n, n)} is the polarity in which n
     * occurs in itself.
     *
     * Paths through target do not need to be considered for checking strict positivity: Such a path is
     * the concatenation of paths already considered, and the product of strictly positive polarities is
     * strictly positive again.
     *
     * @param source source node
     * @param target target node
     * @return sum of the polarities of all paths from source to target, {@link Occurrence#UNUSED} if there
     *         is no such path
     */
    public Occurrence transitiveOccurrence(final Node source, final Node target) {
        // Since the polarity of a path extension only depends on the current node and the polarity of the
        // path so far, it suffices to visit each such pair once.
        final Set<PathState> discovered = new HashSet<>();
        final Deque<PathState> todo = new ArrayDeque<>();
        final Consumer<PathState> enqueue = state -> {
            if (discovered.add(state)) {
                todo.push(state);
            }
        };
        this.outEdges(source).forEach((next, occ) -> enqueue.accept(new PathState(next, occ)));
        Occurrence result = Occurrence.UNUSED;
        // MIXED is absorbing, so the search can stop as soon as it is reached
        while (!todo.isEmpty() && result != Occurrence.MIXED) {
            final PathState current = todo.pop();
            if (current.node().equals(target)) {
                result = result.oplus(current.polarity());
            } else {
                this.outEdges(current.node()).forEach((next, occ) -> enqueue.accept(new PathState(next, current.polarity().otimes(occ))));
            }
        }
        return result;
    }

    @Override
    public String toString() {
        final StringBuilder sb = new StringBuilder();
        for (final Map.Entry<Node, Map<Node, Occurrence>> outgoing : this.edges.entrySet()) {
            for (final Map.Entry<Node, Occurrence> edge : outgoing.getValue().entrySet()) {
                sb.append("  ").append(outgoing.getKey())
                  .append(" -[").append(edge.getValue().toPrettyString()).append("]-> ")
                  .append(edge.getKey()).append("\n");
            }
        }
        return sb.length() == 0 ? "  (empty graph)\n" : sb.toString();
    }

    /**
     * A node of an {@link OccurrenceGraph}, e.g., {@code data Foo a} is represented by the node for the
     * entity of {@code Foo}. Entities do not override {@link Object#equals(Object)}, so nodes are compared
     * by object identity. As every declared type has its own entity, equally named types of different
     * modules are different nodes.
     *
     * @param type entity of the defined type
     */
    public record Node(HaskellEntity type) {
        @Override
        public String toString() {
            return OccurrenceGraph.qualifiedName(this.type);
        }
    }

    /**
     * @return the name of the given type qualified by its module, e.g., {@code Main.Foo}
     */
    static String qualifiedName(final HaskellEntity type) {
        return type.getModule() == null ? type.getName() : type.getModule().getName() + "." + type.getName();
    }
}
