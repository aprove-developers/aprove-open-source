package aprove.verification.oldframework.Haskell.Positivity;

import java.util.*;

import aprove.input.Generated.haskell.node.Token;
import aprove.verification.oldframework.Haskell.Declarations.*;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Positivity.OccurrenceGraph.*;

/**
 * Checks that all data types declared in a Haskell program are strictly positive, i.e., that no declared
 * type occurs in its own definition to the left of an arrow (directly or via other declarations).
 *
 * The notion of H-termination is only sensible for strictly positive data types, so programs violating
 * this restriction are rejected.
 */
public final class PositivityChecker {

    private PositivityChecker() {
    }

    /**
     * Checks all data and newtype declarations of the given modules. The types of the Prelude are taken
     * into account for determining how they use their arguments, but they are not checked themselves.
     *
     * @param modules the modules of the program, already processed by {@link Modules#buildHaskellProgram()}
     * @throws StrictPositivityException if some data type declared outside of the Prelude is not strictly
     *         positive
     */
    public static void check(final Modules modules) {
        final Set<Module> allModules = new LinkedHashSet<>(modules.getModMap().values());
        allModules.add(modules.getPrelude());
        final List<TyConsEntity> types = new ArrayList<>();
        for (final Module module : allModules) {
            for (final HaskellEntity entity : module.getTopEntities()) {
                if (entity instanceof final TyConsEntity type && type.getValue() instanceof DataDecl) {
                    types.add(type);
                }
            }
        }

        final OccurrenceGraph graph = GraphBuilder.build(types);

        final List<Violation> violations = new ArrayList<>();
        for (final TyConsEntity type : types) {
            // FIXME: IOResult in Prelude has a negative self-cycle and MIXED polarity, so we skip this for now (though unsound)
            if (!type.getModule().isPrelude()) {
                final Node node = new Node(type);
                final Occurrence selfOccurrence = graph.transitiveOccurrence(node, node);
                if (selfOccurrence.isNotStrictlyPositive()) {
                    violations.add(new Violation(type, selfOccurrence));
                }
            }
        }

        if (!violations.isEmpty()) {
            final StringBuilder sb = new StringBuilder("Strict positivity check failed:");
            for (final Violation violation : violations) {
                sb.append("\n  ").append(violation);
            }
            throw new StrictPositivityException(violations.get(0).token(), sb.toString());
        }
    }

    /**
     * A data type that occurs in its own definition with a polarity that is not strictly positive.
     *
     * @param type the entity of the data type
     * @param selfOccurrence the polarity in which it occurs in itself
     */
    private record Violation(HaskellEntity type, Occurrence selfOccurrence) {

        /**
         * @return the token of the name of the data type in its declaration, may be {@code null}
         */
        Token token() {
            return GraphBuilder.defType(this.type).getToken();
        }

        @Override
        public String toString() {
            final Token token = this.token();
            return OccurrenceGraph.qualifiedName(this.type) + (token == null ? "" : " at line " + token.getLine())
                    + " is not strictly positive (self-occurrence polarity: " + this.selfOccurrence.toPrettyString() + ")";
        }
    }
}
