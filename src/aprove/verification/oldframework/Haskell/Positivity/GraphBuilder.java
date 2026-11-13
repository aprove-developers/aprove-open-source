package aprove.verification.oldframework.Haskell.Positivity;

import java.util.*;

import aprove.verification.oldframework.Haskell.*;
import aprove.verification.oldframework.Haskell.BasicTerms.*;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Positivity.OccurrenceGraph.*;
import aprove.verification.oldframework.Haskell.Typing.*;

/**
 * Builds the {@link OccurrenceGraph} for a set of data declarations. Types are identified by their
 * entities, so equally named types of different modules are distinguished. The declarations must already
 * be processed by {@link Modules#buildHaskellProgram()}, which resolves the type constructors to their
 * entities and computes the types of the data constructors, where all type synonyms are expanded. Hence,
 * type synonyms do not occur here, e.g., {@code type F = Maybe} and {@code type F a = Maybe a} are the same.
 *
 * For each declaration of a type {@code T}, every type {@code S} occurring in the type of a constructor
 * yields an edge {@code S -[p]-> T}, where {@code p} is the polarity of that occurrence.
 *
 * The polarity of an occurrence inside an argument of a type constructor {@code S} depends on how
 * {@code S} uses its parameter. For declared types, this is the summary of all occurrences of that
 * parameter in the declaration of {@code S}. E.g., for {@code data Func a b = Func (a -> b)}, the
 * summary of {@code Func} stores that {@code a} occurs negatively and {@code b} strictly positively in
 * {@code Func}.
 *
 * Since these summaries might depend on each other for (mutually) recursive or nested declarations,
 * they are computed as a fixpoint. When building the graph, these summaries are used to add the edges
 * for types occurring in arguments of type constructors, e.g., walking {@code Func T Int} in
 * {@code data U = U (Func T Int)} yields {@code T -[-]-> U}. This applies to everything occurring in an
 * argument, whereas the parameters themselves are not part of the graph.
 *
 * The types of the Prelude are passed in as declarations as well, so that their summaries are computed
 * in the same way. Only the built-in type constructors without a declaration are handled explicitly.
 *
 * The occurrence graph and the polarities follow the positivity checker of Agda, see
 * {@code Agda.TypeChecking.Positivity}. In contrast to Agda, where arguments of types of the same mutual
 * block are routed through nodes for the parameters, the summaries are used for all types.
 */
public final class GraphBuilder {

    private static final String ARROW = "->";

    private static final String LIST = "[]";

    /** Tuple type constructors are named @2, @3, ..., see Prelude.createTuple. */
    private static final String TUPLE_PREFIX = "@";

    private GraphBuilder() {
    }

    /**
     * The current approximation of the summaries, i.e., of the polarity in which each parameter of a declared
     * type occurs in its declaration. Initially, the parameters are assumed not to occur at all. As the
     * approximations can only decrease and the lattice of polarities is finite, the fixpoint is reached
     * after finitely many walks over the declarations.
     */
    private static final class Summaries {

        private final Map<HaskellEntity, Occurrence[]> polarities = new HashMap<>();

        private boolean changed = false;

        /**
         * Registers the given data type, initialising the polarity of each parameter to
         * {@link Occurrence#UNUSED}.
         */
        void declare(final HaskellEntity type) {
            final int typeArity = HaskellTools.applyFlatten(GraphBuilder.defType(type)).size() - 1;
            final Occurrence[] approximation = new Occurrence[typeArity];
            Arrays.fill(approximation, Occurrence.UNUSED);
            this.polarities.put(type, approximation);
        }

        /**
         * @return the approximation for the parameters of the given type, {@code null} if it is not declared
         */
        Occurrence[] get(final HaskellEntity type) {
            return this.polarities.get(type);
        }

        /**
         * Adds an occurrence with polarity pol of the parameter at the given index of the given type.
         */
        void addOccurrence(final HaskellEntity type, final int index, final Occurrence pol) {
            final Occurrence[] approximation = this.polarities.get(type);
            final Occurrence updated = approximation[index].oplus(pol);
            if (updated != approximation[index]) {
                approximation[index] = updated;
                this.changed = true;
            }
        }

        /**
         * @return true iff some approximation changed since the last call of this method
         */
        boolean resetChanged() {
            final boolean result = this.changed;
            this.changed = false;
            return result;
        }
    }

    /**
     * Context for walking the right-hand side of one declaration.
     *
     * @param graph the graph to which the edges are added
     * @param summaries the current approximation of the parameter polarities of all declared types
     * @param def the declared type
     * @param paramIndex maps the type parameters of the declaration to their position
     */
    private record Walk(OccurrenceGraph graph, Summaries summaries, HaskellEntity def, Map<String, Integer> paramIndex) {
    }

    /**
     * Builds the occurrence graph of the given types.
     *
     * @param types entities of data and newtype declarations
     * @return the occurrence graph
     */
    public static OccurrenceGraph build(final Collection<TyConsEntity> types) {
        final Summaries summaries = new Summaries();
        for (final TyConsEntity type : types) {
            summaries.declare(type);
        }
        OccurrenceGraph graph;
        do {
            graph = GraphBuilder.buildGraph(types, summaries);
        } while (summaries.resetChanged());
        return graph;
    }

    /**
     * @param type the entity of a data type
     * @return the left-hand side of its declaration, e.g., {@code Foo a b}
     */
    static HaskellObject defType(final HaskellEntity type) {
        return ((DataDecl) type.getValue()).getDefType();
    }

    /**
     * Builds an occurrence graph based on the given approximation of the parameter polarities and adds
     * the occurrences of the parameters to that approximation.
     */
    private static OccurrenceGraph buildGraph(final Collection<TyConsEntity> types, final Summaries summaries) {
        final OccurrenceGraph graph = new OccurrenceGraph();
        for (final TyConsEntity type : types) {
            for (final ConsEntity constructor : type.getConsList()) {
                // e.g. for Cons :: a -> List a -> List a we walk through a and (List a)
                final List<HaskellObject> flattened = GraphBuilder.arrowFlatten(((TypeSchema) constructor.getType()).getMatrix());
                final int fields = flattened.size() - 1;
                final Walk walk = GraphBuilder.startWalk(graph, summaries, type, flattened.get(fields));
                for (final HaskellObject fieldType : flattened.subList(0, fields)) {
                    GraphBuilder.walkType(fieldType, Occurrence.STRICT_POS, walk);
                }
            }
        }
        return graph;
    }

    /**
     * @param type a type {@code t1 -> ... -> tn -> t}, where {@code t} is not a function type
     * @return the list {@code [t1, ..., tn, t]}
     */
    private static List<HaskellObject> arrowFlatten(final HaskellObject type) {
        final List<HaskellObject> flattened = HaskellTools.applyFlatten(type);
        if (flattened.size() == 3 && flattened.get(0) instanceof final Cons cons
                && GraphBuilder.isBuiltinWithName(cons.getSymbol().getEntity(), GraphBuilder.ARROW)) {
            final List<HaskellObject> result = new ArrayList<>();
            result.add(flattened.get(1));
            result.addAll(GraphBuilder.arrowFlatten(flattened.get(2)));
            return result;
        }
        return List.of(type);
    }

    /**
     * Creates the context for walking a constructor of the given type with the given result type,
     * e.g., for {@code Either a b}, the parameter index maps {@code a} to 0 and {@code b} to 1.
     */
    private static Walk startWalk(final OccurrenceGraph graph, final Summaries summaries, final HaskellEntity type, final HaskellObject result) {
        final Map<String, Integer> paramIndex = new LinkedHashMap<>();
        final List<HaskellObject> flattened = HaskellTools.applyFlatten(result);
        final List<HaskellObject> params = flattened.subList(1, flattened.size());
        for (int i = 0; i < params.size(); i++) {
            // the result type of a constructor only has type variables as arguments
            paramIndex.put(((Var) params.get(i)).getSymbol().toString(), i);
        }
        return new Walk(graph, summaries, type, paramIndex);
    }

    /**
     * Walks a type in the walked declaration, e.g., the type of a constructor field: Adds edges
     * to the declared type for all types occurring in it and records the occurrences of the parameters of
     * the declared type.
     *
     * @param type the type to traverse
     * @param pol polarity of the position of type within the walked declaration
     * @param walk the declaration that is walked
     */
    private static void walkType(final HaskellObject type, final Occurrence pol, final Walk walk) {
        final List<HaskellObject> flattened = HaskellTools.applyFlatten(type);
        final HaskellObject head = flattened.get(0);
        final List<HaskellObject> args = flattened.subList(1, flattened.size());
        final Node target = new Node(walk.def());

        if (head instanceof final Cons cons) {
            final HaskellEntity entity = cons.getSymbol().getEntity();
            if (GraphBuilder.isBuiltinWithName(entity, GraphBuilder.ARROW)) {
                GraphBuilder.walkArrow(args, pol, walk);
                return;
            }
            // a type constructor, e.g., walking List T in data U = U (List T) yields List -[++]-> U and T -[p]-> U,
            // where p is the summary of how List uses its parameter
            final Occurrence[] declaredPolarities = entity == null ? null : walk.summaries().get(entity);
            if (entity != null) {
                walk.graph().addEdge(new Node(entity), target, pol);
            }
            for (int i = 0; i < args.size(); i++) {
                final Occurrence argPol;
                if (declaredPolarities != null) {
                    argPol = declaredPolarities[i];
                } else if (GraphBuilder.isBuiltinWithName(entity, GraphBuilder.LIST) || GraphBuilder.isBuiltinTuple(entity)) {
                    // Lists and tuples are built into the Prelude without a declaration, see Prelude.createList
                    // and Prelude.createTuple, so there is no summary for them. They contain their arguments
                    // directly, e.g., [T] or (T, Int).
                    argPol = Occurrence.STRICT_POS;
                } else {
                    // unknown type constructor
                    argPol = Occurrence.MIXED;
                }
                GraphBuilder.walkType(args.get(i), pol.otimes(argPol), walk);
            }
        } else {
            // a type variable, possibly applied, e.g., walking a in data Box a = Box a records that the
            // parameter of Box occurs strictly positively
            if (head instanceof final Var var) {
                final Integer index = walk.paramIndex().get(var.getSymbol().toString());
                if (index != null) {
                    walk.summaries().addOccurrence(walk.def(), index, pol);
                }
            }
            // We do not know how a type variable uses its arguments, so they are treated as occurring in
            // mixed polarity, e.g., data Fix f = Fix (f (Fix f)) is rejected.
            for (final HaskellObject arg : args) {
                GraphBuilder.walkType(arg, pol.otimes(Occurrence.MIXED), walk);
            }
        }
    }

    /**
     * Handles a function type {@code a -> b}: The domain occurs negatively, the codomain keeps the
     * polarity, e.g., walking {@code T -> U} in {@code data U = U (T -> U)} yields {@code T -[-]-> U} and
     * {@code U -[++]-> U}. The arrow may also be partially applied, e.g., {@code (->) a}.
     */
    private static void walkArrow(final List<HaskellObject> args, final Occurrence pol, final Walk walk) {
        if (args.size() > 0) {
            GraphBuilder.walkType(args.get(0), pol.otimes(Occurrence.JUST_NEG), walk);
        }
        if (args.size() > 1) {
            GraphBuilder.walkType(args.get(1), pol, walk);
        }
    }

    /**
     * Built-in types are the types of the Prelude without a declaration, e.g., the function arrow, lists and
     * tuples (see the uses of Prelude.preDefTyCons).
     */
    private static boolean isBuiltin(final HaskellEntity entity) {
        return entity != null && entity.getValue() == null && entity.getModule() != null && entity.getModule().isPrelude();
    }

    private static boolean isBuiltinWithName(final HaskellEntity entity, final String name) {
        return GraphBuilder.isBuiltin(entity) && entity.getName().equals(name);
    }

    private static boolean isBuiltinTuple(final HaskellEntity entity) {
        return GraphBuilder.isBuiltin(entity) && entity.getName().startsWith(GraphBuilder.TUPLE_PREFIX);
    }
}
