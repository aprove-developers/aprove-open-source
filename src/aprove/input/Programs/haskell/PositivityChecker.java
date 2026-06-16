package aprove.input.Programs.haskell;

import aprove.verification.dpframework.HaskellProblem.HaskellProgram;
import aprove.verification.oldframework.Haskell.Declarations.DataDecl;
import aprove.verification.oldframework.Haskell.Declarations.HaskellDecl;
import aprove.verification.oldframework.Haskell.Modules.HaskellEntity;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Haskell.Modules.Modules;
import aprove.verification.oldframework.Haskell.Modules.TyConsEntity;

import java.util.*;

public class PositivityChecker {

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

        GraphBuilder builder = new GraphBuilder();
        OccurrenceGraph graph = builder.buildFromDataDecl(dataDecl);

        List<Violation> violations = new ArrayList<>();
        Map<String, Occurrence> selfLoops = new LinkedHashMap<>();

        for (DataDecl d : dataDecl) {
            var defNode = new OccurrenceGraph.DefNode(typeName(d));
            var loop = graph.transitiveOccurrence(defNode, defNode);
            selfLoops.put(typeName(d), loop);

            if (loop.isNotStrictlyPositive()) {
                violations.add(new Violation(typeName(d), loop));
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

    public void removeStrictPositives(HaskellProgram program) {
        final Set<HaskellEntity> exportEntities = program.getModules().getMainModule().getExportEntities();
        final List<TyConsEntity> consEntityList = exportEntities.stream()
                .filter(cons -> cons instanceof TyConsEntity)
                .map(cons -> (TyConsEntity) cons)
                .toList();
        final GraphBuilder graphBuilder = new GraphBuilder();
        final OccurrenceGraph graph = graphBuilder.buildFromTyConsEntity(consEntityList);
        List<TyConsEntity> removeList = new ArrayList<>();

        for (TyConsEntity cons : consEntityList) {
            var defNode = new OccurrenceGraph.DefNode(cons.getName());
            var loop = graph.transitiveOccurrence(defNode, defNode);

            if (loop.isNotStrictlyPositive()) {
                removeList.add(cons);
            }
        }

        Set<HaskellEntity> newSet = new HashSet<>();

        for (HaskellEntity cons : exportEntities) {
            if (!(cons instanceof TyConsEntity)) {
                newSet.add(cons);
            } else if (!removeList.contains(cons)) {
                newSet.add(cons);
            }

        }

        program.getModules().getMainModule().setExportEntities(newSet);
//            program.getModules().getMainModule().setExpEntities(newSet);
    }

    public void removeStrictPositives(Modules modules) {
//        debug(modules);
        final List<HaskellDecl> decls = modules.getMainModule().getDecls();
        final List<DataDecl> dataDecl = decls.stream()
                .filter(decl -> decl instanceof DataDecl)
                .map(decl -> (DataDecl) decl)
                .toList();

        GraphBuilder builder = new GraphBuilder();
        OccurrenceGraph graph = builder.buildFromDataDecl(dataDecl);

        Set<String> notStrictPositive = new HashSet<>();
        for (DataDecl d : dataDecl) {
            String s = typeName(d);
            var defNode = new OccurrenceGraph.DefNode(s);
            if (graph.transitiveOccurrence(defNode, defNode).isNotStrictlyPositive()) {
                notStrictPositive.add(s);
            }
        }

        List<HaskellDecl> newList = new ArrayList<>();

        for (HaskellDecl decl : decls) {
            if (!(decl instanceof DataDecl dd) || !notStrictPositive.contains(typeName(dd))) {
                newList.add(decl);
            }
        }


        modules.getMainModule().setDecls(newList);
//        debug(modules);
    }

    private String typeName(DataDecl decl) {
        return decl.getDefType().getToken().getText();
    }

    public record Violation(String datatypeName, Occurrence loopOccurrence) {
        @Override
        public String toString() {
            return datatypeName + " is not strictly positive" +
                    " (self-loop polarity = " + loopOccurrence.toString() + ")";
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
