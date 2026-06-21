package aprove.input.Programs.haskell;

import aprove.verification.oldframework.Haskell.Declarations.DataDecl;
import aprove.verification.oldframework.Haskell.Declarations.HaskellDecl;
import aprove.verification.oldframework.Haskell.Declarations.SynTypeDecl;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Modules.Modules;

import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

public class PositivityChecker {

    private static String typeName(DataDecl decl) {
        return decl.getDefType().getToken().getText();
    }

    private Result computeResult(Modules mods) {

        final Map<String, Module> modMap = mods.getModMap();
        final List<HaskellDecl> decls = new ArrayList<>(List.of());

        for (var module : modMap.values()) {
            decls.addAll(module.getDecls());
        }


        final List<DataDecl> dataDecl = decls.stream()
                .filter(decl -> decl instanceof DataDecl)
                .map(decl -> (DataDecl) decl)
                .toList();

        final List<SynTypeDecl> synTypeDecls = decls.stream()
                .filter(decl -> decl instanceof SynTypeDecl)
                .map(decl -> (SynTypeDecl) decl)
                .toList();

        GraphBuilder builder = new GraphBuilder();
        OccurrenceGraph graph = builder.buildFromDataDecl(dataDecl, synTypeDecls);

        List<Violation> violations = new ArrayList<>();
        Map<String, Occurrence> selfLoops = new LinkedHashMap<>();

        for (DataDecl d : dataDecl) {
            var defNode = new OccurrenceGraph.DefNode(typeName(d));
            var loop = graph.transitiveOccurrence(defNode, defNode);
            selfLoops.put(typeName(d), loop);

            if (loop.isNotStrictlyPositive()) {
                violations.add(new Violation(d, loop));
            }
        }

        return new Result(graph, violations, selfLoops);
    }

    public void check(Modules mods) throws StrictPositivityException {
//        debug(mods);
        Result result = computeResult(mods);
        if (!result.isValid()) {
            StringBuilder sb = new StringBuilder();
            sb.append("Strict positivity check failed:\n");
            result.violations().forEach(v -> sb.append("  ").append(v).append("\n"));
            throw new StrictPositivityException(sb.toString());
        }
    }

    public void debug(Modules mods) {
        System.out.println("=== Positivity check ===");
        Result result = computeResult(mods);

        System.out.println("Occurrence graph:");
        System.out.println(result.graph.toStringWithoutUnused());

        System.out.println("Self-loop polarities:");
        for (Map.Entry<String, Occurrence> entry : result.selfLoops().entrySet()) {
            String name = entry.getKey();
            Occurrence occ = entry.getValue();
            System.out.println(name + ": " + occ);
        }

        if (result.isValid()) {
            System.out.println("RESULT: PASSED (strictly positive)");
        } else {
            System.out.println("RESULT: FAILED");
            result.violations().forEach(v -> System.out.println("  " + v));
        }

        System.out.println();
    }

    public record Violation(DataDecl datatype, Occurrence loopOccurrence) {
        @Override
        public String toString() {
            return typeName(datatype) + " is not strictly positive" +
                    " (self-loop polarity = " + loopOccurrence.toString() + ")";
        }

        public DataDecl decl() {
            return datatype;
        }

        public Occurrence occ() {
            return loopOccurrence;
        }
    }

    public record Result(
            OccurrenceGraph graph,
            List<Violation> violations,
            Map<String, Occurrence> selfLoops
    ) {
        public boolean isValid() {
            return violations.isEmpty();
        }
    }
}
