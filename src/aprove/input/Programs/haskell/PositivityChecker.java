package aprove.input.Programs.haskell;

import aprove.verification.oldframework.Haskell.BasicTerms.Apply;
import aprove.verification.oldframework.Haskell.BasicTerms.Cons;
import aprove.verification.oldframework.Haskell.Declarations.DataDecl;
import aprove.verification.oldframework.Haskell.Declarations.HaskellDecl;
import aprove.verification.oldframework.Haskell.Declarations.SynTypeDecl;
import aprove.verification.oldframework.Haskell.Expressions.HaskellExp;
import aprove.verification.oldframework.Haskell.HaskellObject;
import aprove.verification.oldframework.Haskell.Modules.*;
import aprove.verification.oldframework.Haskell.Modules.Module;
import aprove.verification.oldframework.Utility.GenericStructures.Pair;

import java.util.*;

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
// may be helpful to have the prelude types in the graph, but not for now not consistent (e.g. Nat is not exported therefore Int not handled correctly)
//        final Set<HaskellEntity> entities = mods.getPrelude().getExpEntities();
//        final HashMap<String, TyConsEntity> preludeTyCons = new HashMap<>();
//        for (HaskellEntity entity : entities) {
//            if (entity instanceof TyConsEntity tyConsEntity && !Objects.equals(entity.getName(), "->")) {
//                preludeTyCons.put(tyConsEntity.getName(), tyConsEntity);
//            }
//        }

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
//        OccurrenceGraph graph = builder.buildFromDataDecl(dataDecl, synTypeDecls, preludeTyCons);

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

    private void walkType(HaskellObject type){
        if (type instanceof Cons cons && cons.getSymbol().toString().equals("IOResult") && cons.getSymbol().getEntity().getModule().equals("Prelude")) throw new StrictPositivityException("IOResult type is not strictly positive");
        else if (type instanceof Apply apply) {
            walkType(apply.getFunction());
            walkType(apply.getArgument());
        }
    }

    public void checkForIOResult(Modules mods) {
        Module main = mods.getMainModule();
        List<Pair<HaskellObject, HaskellExp>> startTerms = mods.getStartTerms();
        for (Pair<HaskellObject, HaskellExp> startTerm : startTerms) {
            walkType(startTerm.getValue().getTypeTerm());
        }
        for (HaskellEntity entity : main.getExpEntities()) {
            if (entity.getName().equals("IOResult")) continue; // then it is user defined and was checked previously
            else if (entity instanceof ConsEntity consEntity) walkType(consEntity.getType());
            else if (entity instanceof VarEntity varEntity) walkType(varEntity.getValue().getTypeTerm());
        }
    }

    public void debug(Modules mods) {
        System.out.println("=== Positivity check ===");
        Result result = computeResult(mods);

        System.out.println("Occurrence graph:");
//        System.out.println(result.graph.toStringWithoutUnused());
        System.out.println(result.graph);

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
//            return typeName(datatype) + " is not strictly positive" +
//                    " (self-loop polarity = " + loopOccurrence.toString() + ")";
            return typeName(datatype) + " at line " + datatype.getToken().getLine() + " is not strictly positive" +
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
