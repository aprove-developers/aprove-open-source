package aprove.api.examples;

import java.util.*;
import java.util.logging.*;

import aprove.api.*;
import aprove.api.details.*;
import aprove.api.prooftree.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;

/**
 * Runnable example: analyze a simple TRS via the programmatic API.
 *
 * The system is:  f(s(x)) -> f(x)
 *                 f(0)    -> 0
 */
public class ApiExampleTRS {

    public static void main(String[] args) throws Exception {
        suppressLogging();

        FunctionSymbol f    = FunctionSymbol.create("f", 1);
        FunctionSymbol succ = FunctionSymbol.create("s", 1);
        FunctionSymbol zero = FunctionSymbol.create("0", 0);
        TRSVariable    x    = TRSVariable.createVariable("x");

        TRSFunctionApplication zeroTerm = TRSTerm.createFunctionApplication(zero);
        TRSFunctionApplication lhs1 = TRSTerm.createFunctionApplication(f,
            TRSTerm.createFunctionApplication(succ, x));
        TRSFunctionApplication rhs1 = TRSTerm.createFunctionApplication(f, x);
        Rule stepRule = Rule.create(lhs1, rhs1);

        TRSFunctionApplication lhs2 = TRSTerm.createFunctionApplication(f, zeroTerm);
        Rule baseRule = Rule.create(lhs2, zeroTerm);

        AnalyzableProblemInput input = AproveApi.newInstance()
            .newTrsInput()
            .add(stepRule)
            .add(baseRule)
            .name("looped minus one")
            .build();

        long start = System.currentTimeMillis();

        ProofTree tree = input.newProofTreeBuilder()
            .onlineCertificationPath(Optional.empty())
            .onlyCertifiableTechniquesIfPossible(false)
            .strategy(Optional.empty())
            .timeout(Timeout.positiveOrInfinite(60_000))
            .listener(new ProofTreeListener() {
                @Override public void createRoot(ProofTreeNode node) {
                    System.out.println("Analyzing: " + node.getName());
                    printDetail(node.getDetail(Capability.PLAIN), 0);
                    System.out.println("=".repeat(60));
                    System.out.println();
                }
                @Override public void createChild(ProofTreeNode node) {
                    int d = depth(node);
                    System.out.println("  ".repeat(d) + "Obligation: " + node.getName());
                    printDetail(node.getDetail(Capability.PLAIN), d);
                }
                @Override public void createProof(ProofTreeNode node) {
                    node.getProof().ifPresent(proof -> {
                        int d = depth(node);
                        System.out.println("  ".repeat(d) + "[" + proof.getName() + "] " + proof.getImplication());
                        printDetail(proof.getDetail(Capability.PLAIN), d);
                    });
                }
                @Override public void setTruth(ProofTreeNode node, String truth) {}
                @Override public void setComplexity(ProofTreeNode node, String asymptotic, String concrete) {}
                @Override public void setCertificationState(ProofTreeNode node, CPFCheckResult state) {}

                private void printDetail(Detail detail, int depth) {
                    detail.getDetailString().ifPresent(text -> {
                        String indent = "  ".repeat(depth) + "  ";
                        for (String line : text.split("\n")) {
                            if (!line.trim().isEmpty()) {
                                System.out.println(indent + line.stripTrailing());
                            }
                        }
                        System.out.println();
                    });
                }

                private int depth(ProofTreeNode node) {
                    int d = 0;
                    Optional<ProofTreeNode> p = node.getParent();
                    while (p.isPresent()) { d++; p = p.get().getParent(); }
                    return d;
                }
            })
            .construct();

        String result = tree.runAsync().get();
        long elapsed = System.currentTimeMillis() - start;
        System.out.println("=".repeat(60));
        System.out.println("Result: " + result + " (" + elapsed + "ms)");
    }

    private static void suppressLogging() {
        Logger root = Logger.getLogger("");
        root.setLevel(Level.SEVERE);
        for (Handler h : root.getHandlers()) {
            h.setLevel(Level.SEVERE);
        }
    }
}
