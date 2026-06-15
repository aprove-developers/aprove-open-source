package aprove.input.Programs.haskell;

import java.util.*;

/**
 * Graph consisting of DefNode and ArgNode with directed edges between them.
 * Each edge has a certain polarity (Occurrence)
 */
public class OccurrenceGraph {

    // adjacency map edges
    // we map a src -> (target -> occurrence)
    private final Map<Node, Map<Node, Occurrence>> edges = new LinkedHashMap<>();
    //nodes
    private final Set<Node> nodes = new LinkedHashSet<>();

    /**
     * Adds a new edge to the graph
     *
     * @param source source node
     * @param target target node
     * @param occ    polarity of the node
     */
    public void addEdge(Node source, Node target, Occurrence occ) {

        nodes.add(source);
        nodes.add(target);

        edges
                .computeIfAbsent(source, k -> new LinkedHashMap<>())
                .merge(target, occ, Occurrence::oplus);

    }

    /**
     * Simple getter for all the nodes
     *
     * @return unmodifiable set of all the nodes in the graph
     */
    public Set<Node> nodes() {
        return Collections.unmodifiableSet(nodes);
    }

    /**
     *
     *
     * Returns the polarity of the direct edge (source -> target), returns UNUSED if no
     * such edge exists
     *
     * @param source source node
     * @param target target node
     * @return polarity of the direct edge between source and target
     */
    public Occurrence directEdge(Node source, Node target) {
        return edges
                .getOrDefault(source, Map.of())
                .getOrDefault(target, Occurrence.UNUSED);
    }

    /**
     *
     * Returns all edges going out of the given node
     *
     * @param source node of the occurrence graph
     * @return edges having the given node as source
     */
    public Map<Node, Occurrence> outEdges(Node source) {
        return edges.getOrDefault(source, Map.of());
    }

    /**
     * multiplies all path polarities between source and target, using a dfs
     *
     * @param source source node
     * @param target target node
     * @return product of all path polarities
     */
    public Occurrence transitiveOccurrence(Node source, Node target) {
        //DFS: seen = pairs already explored
        Set<Map.Entry<Occurrence, Node>> seen = new HashSet<>();
        return dfs(source, target, Optional.empty(), Optional.empty(), seen).orElse(Occurrence.STRICT_POS);
    }

    /**
     * Depth-first search (recursive) used to find all paths between two nodes and sums the polarities of each path
     * to then multiply the polarities of the paths
     *
     * @param current current node
     * @param target  target node
     * @param pathPol current path polarity
     * @param acc     accumulator, sum of all already traversed paths
     * @param seen    set of all nodes that were already traversed
     * @return polarity
     */
    private Optional<Occurrence> dfs(
            Node current,
            Node target,
            Optional<Occurrence> pathPol,
            Optional<Occurrence> acc,
            Set<Map.Entry<Occurrence, Node>> seen
    ) {
        if (pathPol.isPresent()) {
            var key = Map.entry(pathPol.get(), current);
            if (seen.contains(key)) return acc;
            seen.add(key);
        }
        if (current.equals(target) && pathPol.isPresent()) {
//            acc = acc.oplus(pathPol); // add the new path to the accumulator
//            if (acc == Occurrence.MIXED) return acc; // can't get worse
            acc = Optional.of(acc
                    .map(a -> a.oplus(pathPol.get()))
                    .orElse(pathPol.get()));
            if (acc.get() == Occurrence.MIXED) return acc; // can't get worse

        }

        // Recurse into neighbours
        for (var entry : outEdges(current).entrySet()) {
            Node next = entry.getKey();
            Occurrence edgeOcc = entry.getValue();
            Occurrence newPath = pathPol
                    .map(p -> p.oplus(edgeOcc))
                    .orElse(edgeOcc);
            if (newPath == Occurrence.UNUSED) continue; //dead path
            acc = dfs(next, target, Optional.of(newPath), acc, seen);
            if (acc.isPresent() && acc.get() == Occurrence.MIXED) return acc;
        }

        return acc;
    }

    public String toStringWithoutUnused() {
        var sb = new StringBuilder();
        for (var src : edges.keySet()) {
            for (var edge : edges.get(src).entrySet()) {
                if (!edge.getValue().equals(Occurrence.UNUSED)) {
                    sb.append("  ").append(src)
                            .append(" -[")
                            .append(edge.getValue().toPrettyString())
                            .append("]-> ")
                            .append(edge.getKey())
                            .append("\n");
                }
            }
        }
        return (sb.length() == 0) ? "  (empty graph)\n" : sb.toString();
    }

    @Override
    public String toString() {
        var sb = new StringBuilder();
        //form: src-[occ]->target
        for (var src : edges.keySet()) {
            for (var edge : edges.get(src).entrySet()) {
                sb.append("  ").append(src)
                        .append(" -[")
                        .append(edge.getValue().toPrettyString())
                        .append("]-> ")
                        .append(edge.getKey())
                        .append("\n");
            }
        }
        return (sb.length() == 0) ? "  (empty graph)\n" : sb.toString();
    }

    public sealed interface Node permits DefNode, ArgNode {
    }

    /**
     * Node in the Occurrence graph for a data definition
     * e.g. `data Foo` => DefNode("Foo")
     *
     * @param name Name of the datatype
     */
    public record DefNode(String name) implements Node {
        @Override
        public String toString() {
            return name;
        }
    }

    /**
     * Node in the Occurrence graph for an argument of a data definition
     * e.g. `data Foo a` => ArgNode("Foo", 0) would represent "a"
     *
     * @param name  Name of the datatype this argument belongs to
     * @param index Index in which this argument appears in the data definition
     */
    public record ArgNode(String name, int index) implements Node {
        @Override
        public String toString() {
            return name + "." + index;
        }
    }

}
