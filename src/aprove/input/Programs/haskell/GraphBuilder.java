package aprove.input.Programs.haskell;

import aprove.verification.oldframework.Haskell.BasicTerms.Apply;
import aprove.verification.oldframework.Haskell.BasicTerms.Cons;
import aprove.verification.oldframework.Haskell.BasicTerms.Var;
import aprove.verification.oldframework.Haskell.Declarations.DataDecl;
import aprove.verification.oldframework.Haskell.Declarations.SynTypeDecl;
import aprove.verification.oldframework.Haskell.HaskellObject;
import aprove.verification.oldframework.Haskell.Modules.TyConsEntity;
import aprove.verification.oldframework.Haskell.Typing.DataCon;

import java.util.*;
import java.util.stream.IntStream;

public class GraphBuilder {
    private final OccurrenceGraph graph;

    private String currentDef;

    private final Set<String> datatypeNames;

    private Map<String, Integer> paramIndex;

    public GraphBuilder() {
        this.datatypeNames = new HashSet<>();
        this.graph = new OccurrenceGraph();
    }

    public OccurrenceGraph buildFromDataDecl(List<DataDecl> dataDecls, List<SynTypeDecl>  synTypeDecls) {
        dataDecls.forEach(d -> datatypeNames.add(d.getDefType().getToken().getText()));
        synTypeDecls.forEach(d -> datatypeNames.add(d.getDefType().getToken().getText()));
        synTypeDecls.forEach(this::processSynTypes);
        dataDecls.forEach(this::processDataDecl);
        return graph;
    }

    public OccurrenceGraph buildFromTyConsEntity(List<TyConsEntity> types) {
        for (TyConsEntity entity : types) {
            datatypeNames.add(entity.getName());
        }

        for (TyConsEntity entity : types) {
            processDataDecl((DataDecl) entity.getValue());
        }

        return graph;
    }

    private void processSynTypes(SynTypeDecl synTypeDecl) {
        currentDef = synTypeDecl.getDefType().getToken().getText();
        paramIndex = new HashMap<>();

        if  (synTypeDecl.getDefType() instanceof Apply apply) {
            //collect vars from data declaration
            List<HaskellObject> vars = new ArrayList<>();
            var _ = flattenApp(apply, vars);

            //add vars to paramIndex with innermost index 0
            IntStream.range(0, vars.size())
                    .forEach(index -> paramIndex.put(((Var) vars.get(index)).getSymbol().toString(), index));
        }

        graph.addEdge(
                new OccurrenceGraph.DefNode(currentDef),
                new OccurrenceGraph.DefNode(currentDef),
                Occurrence.UNUSED
        );

        walkType(
                synTypeDecl.getType(),
                Occurrence.STRICT_POS,
                new OccurrenceGraph.DefNode(currentDef)
        );

    }

    private void processDataDecl(DataDecl dd) {
        //reset
        currentDef = dd.getDefType().getToken().getText();
        paramIndex = new LinkedHashMap<>();

        if (dd.getDefType() instanceof Apply apply) {

            //collect vars from data declaration
            List<HaskellObject> vars = new ArrayList<>();
            var _unusedVar = flattenApp(apply, vars);

            //add vars to paramIndex with innermost index 0
            IntStream.range(0, vars.size())
                    .forEach(index -> paramIndex.put(((Var) vars.get(index)).getSymbol().toString(), index));
        }
        //create node
        graph.addEdge(
                new OccurrenceGraph.DefNode(currentDef),
                new OccurrenceGraph.DefNode(currentDef),
                Occurrence.UNUSED
        );

        for (DataCon ctor : dd.getDataCons()) {
            processConstructor(ctor);
        }

    }

    /**
     * Collects arguments from a data declaration and returns the head of the function
     *
     * @param app  some Apply (e.g. Foo a b c)
     * @param args array storing the arguments (e.g. Foo a b c => args = [a, b, c]
     * @return head (Foo a b c => Foo)
     */
    private HaskellObject flattenApp(Apply app, List<HaskellObject> args) {
        List<HaskellObject> reversed = new ArrayList<>();
        HaskellObject current = app;

        while (current instanceof Apply apply) {
            reversed.add(apply.getArgument());
            current = apply.getFunction();
        }

        for (int i = reversed.size() - 1; i >= 0; i--) {
            args.add(reversed.get(i));
        }

        // System.out.println(args);

        return current;
    }

    private void processConstructor(DataCon ctor) {
        // e.g. data List a = Nil | Cons a (List a)
        // => ctor = `Cons a (List a)`
        // => ctor.getTypes() -> ['a', '(List a)']
        for (var type : ctor.getTypes()) {
            walkType(
                    type,
                    Occurrence.STRICT_POS,
                    new OccurrenceGraph.DefNode(currentDef)
            );
        }
    }

    private void walkType(HaskellObject type, Occurrence pol, OccurrenceGraph.Node target) {
        if (type instanceof Cons cons) {
            walkCons(cons, pol, target);
        } else if (type instanceof Var var) {
            walkVar(var, pol, target);
        } else if (type instanceof Apply apply) {
            walkApply(apply, pol, target);
        }
    }

    // e.g. Foo = mkFoo Bar => cons -> `Bar`
    private void walkCons(Cons cons, Occurrence pol, OccurrenceGraph.Node target) {
        String name = cons.getSymbol().toString();
        if (datatypeNames.contains(name)) {
            graph.addEdge(
                    new OccurrenceGraph.DefNode(name),
                    target,
                    pol
            );
        }
    }

    private void walkVar(Var var, Occurrence pol, OccurrenceGraph.Node target) {
        String name = var.getSymbol().toString();
        if (paramIndex.containsKey(name)) {
            int index = paramIndex.get(name);
            graph.addEdge(
                    new OccurrenceGraph.ArgNode(currentDef, index),
                    target,
                    pol
            );
        }
    }


    private void walkApply(Apply apply, Occurrence pol, OccurrenceGraph.Node target) {
        List<HaskellObject> args = new ArrayList<>();
        var head = flattenApp(apply, args);

        if (head instanceof Cons cons) {

            String name = cons.getSymbol().toString();

            // System.out.println("Assessing "+ apply + ", name: " + name);

            //check if arrow function
            if (name.equals("->")) {
                // System.out.println("WalkArrow called");
                walkArrow(apply, pol, target);
                return;
            }


            if (datatypeNames.contains(name)) {
                graph.addEdge(
                        new OccurrenceGraph.DefNode(name),
                        target,
                        pol
                );
            }

            for (int i = 0; i < args.size(); i++) {
                Occurrence argPol = pol.otimes(argPolarity(name));
                var argTarget = argTarget(name, i, target);
                walkType(args.get(i), argPol, argTarget);
            }
        } else {
            walkType(head, pol, target);
            for (var a : args) {
                walkType(a, pol.otimes(Occurrence.MIXED), target);
            }
        }
    }

    private Occurrence argPolarity(String name) {
        if (datatypeNames.contains(name)) {
//            return Occurrence.GUARD_POS;
            return Occurrence.STRICT_POS;
        }
        return Occurrence.MIXED;
    }

    private OccurrenceGraph.Node argTarget(
            String name, int argIndex, OccurrenceGraph.Node currentTarget
    ) {
        if (datatypeNames.contains(name)) {
            return new OccurrenceGraph.ArgNode(name, argIndex);
        }
        return currentTarget;
    }

    private void walkArrow(Apply apply, Occurrence pol, OccurrenceGraph.Node target) {
        var codomain = apply.getArgument();
        if (apply.getFunction() instanceof Apply apply2) {
            var domain = apply2.getArgument();
            walkType(domain, pol.otimes(Occurrence.JUST_NEG), target);
            walkType(codomain, pol, target);
        } else {
            //should not happen
        }
    }
}
