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

    // future use to handle Prelude
    private final Set<Node> prelimNodes = new LinkedHashSet<>(Set.of(
            new DefNode("ReadS")
            , new DefNode("String")
            , new ArgNode("ReadS", 0)
            , new DefNode("ShowS")
            , new DefNode("Char")
            , new DefNode("Rational")
            , new DefNode("Ratio")
            , new DefNode("Integer")
            , new ArgNode("Ratio", 0)
            , new DefNode("FilePath")
            , new DefNode("WHNF")
            , new ArgNode("WHNF", 0)
            , new DefNode("Nat")
            , new DefNode("Maybe")
            , new ArgNode("Maybe", 0)
            , new DefNode("Either")
            , new ArgNode("Either", 0)
            , new ArgNode("Either", 1)
            , new DefNode("Ordering")
            , new DefNode("Int")
            , new DefNode("Float")
            , new DefNode("Double")
            , new DefNode("IOError")
            , new DefNode("IOErrorKind")
            , new DefNode("Obj")
            , new DefNode("IO")
            , new DefNode("IOResult")
            , new ArgNode("IO", 0)
            , new DefNode("AET")
            , new DefNode("HugsException")
            , new DefNode("IOFinished")
            , new ArgNode("IOFinished", 0)
    ));

    //future use to handle Prelude
    private final Map<Node, Map<Node, Occurrence>> prelimTypeEdges = new LinkedHashMap<>(
            Map.ofEntries(
                    Map.entry(
                            new DefNode("String"),
                            Map.of(
                                    new DefNode("ReadS"), Occurrence.MIXED,
                                    new DefNode("ShowS"), Occurrence.MIXED,
                                    new DefNode("FilePath"), Occurrence.STRICT_POS,
                                    new DefNode("IOError"), Occurrence.STRICT_POS,
                                    new ArgNode("Maybe", 0), Occurrence.STRICT_POS,
                                    new DefNode("IO"), Occurrence.STRICT_POS,
                                    new DefNode("AET"), Occurrence.STRICT_POS
                            )
                    ),
                    Map.entry(
                            new ArgNode("ReadS", 0),
                            Map.of(
                                    new DefNode("ReadS"), Occurrence.MIXED
                            )
                    ),
                    Map.entry(
                            new DefNode("Char"),
                            Map.of(
                                    new DefNode("String"), Occurrence.MIXED
                            )
                    ),
                    Map.entry(
                            new DefNode("Ratio"),
                            Map.of(
                                    new DefNode("Rational"), Occurrence.STRICT_POS
                            )
                    ),
                    Map.entry(
                            new DefNode("Integer"),
                            Map.of(
                                    new ArgNode("Ratio", 0), Occurrence.STRICT_POS
                            )
                    ),
                    Map.entry(
                            new ArgNode("WHNF", 0),
                            Map.of(
                                    new DefNode("WHNF"), Occurrence.STRICT_POS
                            )
                    ),
                    Map.entry(
                            new DefNode("Nat"),
                            Map.of(
                                    new DefNode("Char"), Occurrence.STRICT_POS,
                                    new DefNode("Int"), Occurrence.STRICT_POS,
                                    new DefNode("Nat"), Occurrence.STRICT_POS
                            )
                    ),
                    Map.entry(
                            new ArgNode("Maybe", 0),
                            Map.of(
                                    new DefNode("Maybe"), Occurrence.STRICT_POS
                            )
                    ),
                    Map.entry(
                            new ArgNode("Either", 0),
                            Map.of(
                                    new DefNode("Either"), Occurrence.STRICT_POS
                            )
                    ),
                    Map.entry(
                            new ArgNode("Either", 1),
                            Map.of(
                                    new DefNode("Either"), Occurrence.STRICT_POS
                            )
                    ),
                    Map.entry(
                            new DefNode("Int"),
                            Map.of(
                                    new DefNode("Integer"), Occurrence.STRICT_POS,
                                    new DefNode("Float"), Occurrence.STRICT_POS,
                                    new DefNode("Double"), Occurrence.STRICT_POS,
                                    new DefNode("IOResult"), Occurrence.STRICT_POS,
                                    new DefNode("IOFinished"), Occurrence.STRICT_POS
                            )
                    ),
                    Map.entry(
                            new ArgNode("Ratio", 0),
                            Map.of(
                                    new DefNode("Ratio"), Occurrence.STRICT_POS
                            )
                    ),
                    Map.entry(
                            new DefNode("IOErrorKind"),
                            Map.of(
                                    new DefNode("IOError"), Occurrence.STRICT_POS
                            )
                    ),
                    Map.entry(
                            new DefNode("Maybe"),
                            Map.of(
                                    new DefNode("IOError"), Occurrence.STRICT_POS
                            )
                    ),
                    Map.entry(
                            new DefNode("IOError"),
                            Map.of(
                                    new DefNode("IO"), Occurrence.JUST_POS,
                                    new DefNode("AET"), Occurrence.STRICT_POS,
                                    new DefNode("IOResult"), Occurrence.MIXED,
                                    new DefNode("IOFinished"), Occurrence.STRICT_POS
                            )
                    ),
                    Map.entry(
                            new DefNode("IOResult"),
                            Map.of(
                                    new DefNode("IO"), Occurrence.MIXED,
                                    new DefNode("IOResult"), Occurrence.MIXED
                            )
                    ),
                    Map.entry(
                            new ArgNode("IO", 0),
                            Map.of(
                                    new DefNode("IO"), Occurrence.JUST_POS
                            )
                    ),
                    Map.entry(
                            new DefNode("AET"),
                            Map.of(
                                    new DefNode("IO"), Occurrence.STRICT_POS
                            )
                    ),
                    Map.entry(
                            new DefNode("HugsException"),
                            Map.of(
                                    new DefNode("IOResult"), Occurrence.JUST_NEG
                            )
                    ),
                    Map.entry(
                            new DefNode("Obj"),
                            Map.of(
                                    new DefNode("IOResult"), Occurrence.MIXED
                            )
                    ),
                    Map.entry(
                            new ArgNode("IOFinished", 0),
                            Map.of(
                                    new DefNode("IOFinished"), Occurrence.STRICT_POS
                            )
                    )
            )
    );

    /**
     * Adds a new edge to the graph
     *
     * @param source source node
     * @param target target node
     * @param occ    polarity of the node
     */
    public void addEdge(Node source, Node target, Occurrence occ) {

        if (!nodes.contains(source) && !prelimNodes.contains(source))
            nodes.add(source);
        if (!nodes.contains(target) && !prelimNodes.contains(target))
            nodes.add(target);

        edges
                .computeIfAbsent(source, k -> new LinkedHashMap<>())
                .merge(target, occ, Occurrence::oplus);

    }

    public void addNode(Node node) {
        nodes.add(node);
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
        Set<Map.Entry<Node, Node>> seen = new HashSet<>();
        return dfs(Optional.empty(), source, target, Optional.empty(), Occurrence.UNUSED, seen);
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
    private Occurrence dfs(
            Optional<Node> previous,
            Node current,
            Node target,
            Optional<Occurrence> pathPol,
            Occurrence acc,
            Set<Map.Entry<Node, Node>> seen
    ) {
        if (previous.isPresent()) {
            var key = Map.entry(previous.get(), current);
            if (seen.contains(key)) return acc;
            seen.add(key);
        }
        if (current.equals(target) && pathPol.isPresent()) {
            acc = acc.oplus(pathPol.get());
            if (acc == Occurrence.MIXED) return acc; // can't get worse

        }

        // Recurse into neighbours
        for (var entry : outEdges(current).entrySet()) {
            Node next = entry.getKey();
            Occurrence edgeOcc = entry.getValue();
            Occurrence newPath = pathPol
                    .map(p -> p.otimes(edgeOcc))
                    .orElse(edgeOcc);
            acc = dfs(Optional.of(current), next, target, Optional.of(newPath), acc, seen);
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

    public String prelimGraphToString() {
        var sb = new StringBuilder();
        //form: src-[occ]->target
        for (var node : prelimNodes) {
            sb.append("  ").append(node).append("\n");
        }

        for (var src : prelimTypeEdges.keySet()) {
            for (var edge : prelimTypeEdges.get(src).entrySet()) {
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

    @Override
    public String toString() {
        var sb = new StringBuilder();
        //form: src-[occ]->target
        for (var node : nodes) {
            sb.append("  ").append(node).append("\n");
        }

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
