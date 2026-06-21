package aprove.verification.probabilistic.Termination.PTRSProblem.AST.Processors;

import java.math.*;
import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.solver.Engines.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Algebra.Polynomials.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.*;
import aprove.verification.oldframework.IntTRS.PoloRedPair.CoefficientConstraint.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SMTLIB.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;

/**
 * Processor that decides AST for RNT (right-ground, non-overlapping, tail-recursive) PTRS
 * by using the moment matrix method known from procedures to decide consistency in
 * stochastic context-free grammars.
 *
 * @author Arion Scheid
 * @version $Id$
 */
public class PTRS_AST_DecidableRNTProcessor extends PTRS_AST_ProblemProcessor {


    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isPTRSApplicable(PTRSProblem R) {
        return R.isRightGround() && R.isNonOverlapping() && R.isTailRecursive();
    }


    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    protected Result processPTRSProblem(PTRSProblem R, Abortion aborter) throws AbortionException {
        try {
            // If problem not ground transform to from right ground to ground problem 
            R = R.isGround() ? R : applyTgnt(R);
            assert R.isGround(): "GNT transformation is faulty";
            // T_GNT may return the empty problem if no LHS from the original rules ever appears in any RHS -> trivially terminating       
            if (R.getPR().isEmpty()) {
                return ResultFactory.proved(new ASTDecidableRNTProof("empty", true));
            }

            Set<ProbabilisticRule> remainingRules = new LinkedHashSet<ProbabilisticRule>(R.getPR());
            if (R.isWeaklyNormalizing(remainingRules)) {
                final List<ProbabilisticRule> indexedRules = new ArrayList<ProbabilisticRule>(R.getPR()); // order rules
                final int n = indexedRules.size(); // matrix dimension
                final BigFraction[][] matrix = new BigFraction[n][n];
                Map<String,BigFraction> names = new LinkedHashMap<>(); // placeholder names for probabilities
                for (int i = 0; i<n; i++) { // rows
                    ProbabilisticRule rule = indexedRules.get(i);
                    MultiDistribution<TRSTerm> rhs = rule.getRight();
                    for (int j = 0; j<n; j++) { // columns
                        BigFraction val = BigFraction.ZERO;
                        TRSTerm s = indexedRules.get(j).getLeft();
                        for (Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rhs.getProbabilityMapping().entrySet()) {
                            int m = 0;
                            for (Pair<Position, TRSTerm> t : entry.getKey().x.getPositionsWithSubTerms()) {
                                if (t.y.matches(s)) m++;
                            }
                            if (m == 0) continue;
                            BigFraction addend = entry.getKey().y.multiply(entry.getValue()).multiply(m);
                            val = val.add(addend);
                        }
                        matrix[i][j] = val;
                        names.putIfAbsent(val.toString(),val);
                    }
                }
                YNM res = checkConsistencyOfSubmatrices(matrix,names,aborter);
                switch(res) {
                    case NO -> {
                        return ResultFactory.disproved(new ASTDecidableRNTProof(printMatrix(matrix),false));
                    }
                    case YES -> {
                        return ResultFactory.proved(new ASTDecidableRNTProof(printMatrix(matrix),true));
                    }
                    case MAYBE -> { // should not happen by decidability
                        return ResultFactory.unknown(new ASTDecidableRNTProof(printMatrix(matrix),false));
                    }
                }
                return null; // unreachable

            } else {
                for (ProbabilisticRule rule : remainingRules) {
                    return ResultFactory.disproved(new NotASTDecidableRNTProof(rule.getLeft().toString()));
                }
                return null; // unreachable
            }
        } catch (Exception e) {
            // should not happen since processor only applied when ptrs tail-recursive
            return ResultFactory.error(e);
        }
    } 


    // ================================================================================
    // Utility
    // ================================================================================
    
    private static Set<TRSTerm> computeILhs(PTRSProblem P) {
        Set<TRSTerm> iLhs = new LinkedHashSet<>();
        for (ProbabilisticRule rule : P.getPR()) {
            for (TRSTerm rhs : rule.getRight().getSupport()) {
                for (Pair<Position, TRSTerm> sub : rhs.getPositionsWithSubTerms()) {
                    TRSTerm subterm = sub.y;
                    for (ProbabilisticRule rule2 : P.getPR()) {
                        TRSTerm lhs = rule2.getLeft();
                        // lhs has variables, subterm is ground, match lhs onto subterm
                        TRSSubstitution sigma = subterm.getMatcher(lhs);
                        if (sigma != null) {
                            iLhs.add(subterm);
                            break; // non-overlapping: at most one rule matches
                        }
                    }
                }
            }
        }
        return iLhs;
    }


    private static PTRSProblem applyTgnt(PTRSProblem P) {
        Set<TRSTerm> iLhs = computeILhs(P);
        Set<ProbabilisticRule> newRules = new LinkedHashSet<>();
        for (TRSTerm inst : iLhs) {
            for (ProbabilisticRule rule : P.getPR()) {
                TRSSubstitution sigma = rule.getLeft().getMatcher(inst);
                if (sigma != null) {
                    HashMultiSet<Pair<TRSTerm, BigFraction>> newProbMap = new HashMultiSet<>();
                    for (Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
                        TRSTerm term = entry.getKey().x;
                        BigFraction prob = entry.getKey().y;
                        Integer count = entry.getValue();
                        newProbMap.put(new Pair<>(term.applySubstitution(sigma), prob), count);
                    }
                    MultiDistribution<TRSTerm> instRhs = new MultiDistribution<>(newProbMap);
                    newRules.add(ProbabilisticRule.create((TRSFunctionApplication) inst, instRhs));
                    break; // P is non-overlapping, at most one rule matches
                }
            }
        }
        return new PTRSProblem(newRules, P.getRewriteStrategy(), P.getTarget(), P.isBasic());
    }

    private static YNM checkConsistencyOfMatrix(BigFraction[][] matrix, Map<String,BigFraction> names, Abortion aborter) {
        SimplePolynomial charPolynomial = computeCharacteristicPolynomial(preProc(matrix,names));
        SimplePolynomial normalizedPoly = normalizePolynomial(charPolynomial,names);
        SimplePolynomial leqOnePoly = SimplePolynomial.create("x").minus(SimplePolynomial.create(1));
        YNM res = askSMT(normalizedPoly,leqOnePoly,aborter);
        return res;
    }


    private static YNM checkConsistencyOfSubmatrices(BigFraction[][] matrix, Map<String,BigFraction> names, Abortion aborter) {
        for (BigFraction[][] submatrix : getConnectedComponents(matrix)) {
            YNM res = checkConsistencyOfMatrix(submatrix, names, aborter);
            switch (res) {
                case NO -> {
                    return YNM.NO;
                }
                case YES -> {
                    continue;
                }
                default -> {
                    return YNM.MAYBE;
                }
            }
        }
        return YNM.YES;
    }


    public static Set<BigFraction[][]> getConnectedComponents(BigFraction[][] mat) {
        int n = mat.length;
        boolean[] visited = new boolean[n];
        Set<BigFraction[][]> components = new HashSet<>();

        // Build adjacency list
        List<Integer>[] adj = new List[n];
        for (int i = 0; i < n; i++) adj[i] = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            for (int j = 0; j < n; j++) {
                if (!mat[i][j].equals(BigFraction.ZERO)) {
                    adj[i].add(j);
                    adj[j].add(i); // Treat as undirected
                }
            }
        }

        for (int i = 0; i < n; i++) {
            if (!visited[i]) {
                // Get all nodes in this component
                Set<Integer> componentNodes = new TreeSet<>();
                dfs(i, adj, visited, componentNodes);

                // Extract submatrix
                BigFraction[][] submatrix = extractSubmatrix(mat, componentNodes);
                components.add(submatrix);
            }
        }

        return components;
    }

    private static void dfs(int node, List<Integer>[] adj, boolean[] visited, Set<Integer> component) {
        visited[node] = true;
        component.add(node);
        for (int neighbor : adj[node]) {
            if (!visited[neighbor]) {
                dfs(neighbor, adj, visited, component);
            }
        }
    }

    private static BigFraction[][] extractSubmatrix(BigFraction[][] mat, Set<Integer> indices) {
        int size = indices.size();
        BigFraction[][] sub = new BigFraction[size][size];
        List<Integer> indexList = new ArrayList<>(indices);

        for (int i = 0; i < size; i++) {
            int origI = indexList.get(i);
            for (int j = 0; j < size; j++) {
                int origJ = indexList.get(j);
                sub[i][j] = mat[origI][origJ];
            }
        }
        return sub;
    }


    private static SimplePolynomial normalizePolynomial(SimplePolynomial poly, Map<String,BigFraction> names) {
        BigInteger kgv = BigInteger.ONE; // large overapproximation of actual kgv
        for (IndefinitePart coeff : poly.getSimpleMonomials().keySet()) {
            for (String s : coeff.getIndefinites()) {
                if (s.equals("x")) continue; // names.get("x") is undefined
                kgv = kgv.multiply(names.get(s).getDenominator().pow(coeff.getExponent(s)));
            }
        }
        SimplePolynomial p = poly.times(SimplePolynomial.create(kgv));
        Map<IndefinitePart,BigInteger> res = new LinkedHashMap<>();
        for (IndefinitePart coeff : p.getSimpleMonomials().keySet()) {
            Map<String,Integer> tmp = new LinkedHashMap<>();
            BigInteger val = p.getSimpleMonomials().get(coeff);
            for (String s : coeff.getIndefinites()) {
                if (s.equals("x")) {
                    tmp.put(s, coeff.getExponent(s));
                    continue;
                }
                val = val.divide(names.get(s).getDenominator());
                val = val.multiply(names.get(s).getNumerator());
            }
            IndefinitePart newX = IndefinitePart.create(tmp);
            if (!res.keySet().contains(newX)) {
                res.put(newX, val);
            } else {
                res.put(newX,res.get(newX).add(val));
            }
        }
        return SimplePolynomial.create(res);
    }


    private static SimplePolynomial[][] preProc(BigFraction[][] matrix,
                                                Map<String,BigFraction> names) {
        int n = matrix[0].length;
        Map<String,SimplePolynomial> atoms = new LinkedHashMap<>();
        SimplePolynomial[][] newMatrix = new SimplePolynomial[n][n];
        SimplePolynomial x = SimplePolynomial.create("x");
        atoms.put("x", x);
        for (String name : names.keySet()) {
            if (names.get(name).getDenominator().equals(BigInteger.ONE)) {
                atoms.put(name,SimplePolynomial.create(names.get(name).getNumerator()));
            } else {
                atoms.put(name, SimplePolynomial.create(name));
            }
        }
        for (int i = 0; i<n; i++) {
            for (int j = 0; j<n; j++) {
                if (i == j) {
                    newMatrix[i][j] = atoms.get(matrix[i][j].toString()).minus(x);
                } else {
                    newMatrix[i][j] = atoms.get(matrix[i][j].toString());
                }
            }
        }

        return newMatrix;
    }


    private static SimplePolynomial[][] getMinor(SimplePolynomial[][] matrix,
                                                 int rowToRemove,
                                                 int colToRemove) {
        int n = matrix[0].length;
        SimplePolynomial[][] minor = new SimplePolynomial[n - 1][n - 1];
        int r = 0;

        for (int i = 0; i < n; i++) {
            if (i == rowToRemove) continue;
            int c = 0;
            for (int j = 0; j < n; j++) {
                if (j == colToRemove) continue;
                minor[r][c++] = matrix[i][j];
            }
            r++;
        }
        return minor;
    }


    private static SimplePolynomial computeCharacteristicPolynomial(SimplePolynomial[][] matrix) {
        int n = matrix[0].length;
        if (n == 1) {
            return matrix[0][0];
        }

        if (n == 2) {
            SimplePolynomial res = matrix[0][0].times(matrix[1][1]).minus(matrix[0][1].times(matrix[1][0]));
            return res;
        }

        SimplePolynomial p = SimplePolynomial.create(0);
        for (int j = 0; j < n; j++) {
            SimplePolynomial cofactor = matrix[0][j];
            SimplePolynomial[][] minor = getMinor(matrix,0,j);
            SimplePolynomial minorPol = computeCharacteristicPolynomial(minor);
            SimplePolynomial res = cofactor.times(minorPol);
            if ((j%2) == 0) {
                p = p.plus(res);
            } else {
                p = p.minus(res);
            }
        }

        return p;
    }


    private static <T> String printMatrix(T[][] matrix) {
        if (matrix == null) return "";
        StringBuilder res = new StringBuilder();
        int maxWidth = 0;
        for (T[] row : matrix) {
            for (T val : row) {
                maxWidth = Math.max(maxWidth, val.toString().length());
            }
        }
        for (T[] row : matrix) {
            for (T val : row) {
                res.append(" " + val.toString() + " ");
            }
            res.append("\n");
        }
        return res.toString();
    }

    private static YNM askSMT(SimplePolynomial p1, SimplePolynomial p2, Abortion aborter) {
        CoefficientConstraint c1 = new CoefficientConstraint(p1,CoefficientConstraintType.EQ_ZERO);
        CoefficientConstraint c2 = new CoefficientConstraint(p2,CoefficientConstraintType.GT_ZERO);
        SMTLIBTheoryAtom a1 = c1.toSMTLIBRatTheoryAtom();
        SMTLIBTheoryAtom a2 = c2.toSMTLIBRatTheoryAtom();
        final FormulaFactory<SMTLIBTheoryAtom> factory =
                new FullSharingFactory<SMTLIBTheoryAtom>();
        final LinkedList<Formula<SMTLIBTheoryAtom>> formulae =
                new LinkedList<>();
        formulae.add(factory.buildTheoryAtom(a1));
        formulae.add(factory.buildTheoryAtom(a2));
        SMTLIBEngine solver = new SMTLIBEngine();
        YNM answer;
        try {
            answer = solver.satisfiable(formulae, SMTEngine.SMTLogic.QF_RA, aborter);
        } catch (final WrongLogicException e) {
            answer = YNM.MAYBE;
        }
        switch (answer) {
            case YES -> {
                return YNM.NO;
                }
            case NO -> {
                return YNM.YES;
                }
            default -> {
                return YNM.MAYBE;
                }
        }

    }


    // ================================================================================
    // Proof
    // ================================================================================


    private class ASTDecidableRNTProof extends Proof.DefaultProof {

        final String matrix;
        final boolean ast;

        public ASTDecidableRNTProof(String s, boolean ast) {
            super();
            this.matrix = s;
            this.ast = ast;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder proof = new StringBuilder();
            proof.append(o.export("For n rules, we construct the n x n moment matrix B(1) "+ o.cite(Citation.EY09) + ", which captures termination probabilities of lhs.\n"));
            proof.append(o.export("The technique originates from the analysis of stochastic context-free grammars and is applicable as stated below in (*).\n"));
            proof.append(o.export("The resulting matrix looks like the following"));
            proof.append(o.newline());
            proof.append(o.export(matrix));
            proof.append(o.newline());
            proof.append(o.export("Now the matrix is split into its connected components (CCs) and for each we determine whether its eigenvalue is <= 1.\n"));
            proof.append(o.export("(*) The system is right-ground, non-overlapping and tail-recursive, so it is AST iff the maximum eigenvalue of all CCs is <= 1\n"));
            String maybeNot = this.ast? "" : "not ";
            proof.append(o.export("Since " + maybeNot + "all CCs had eigenvalue <= 1, the PTRS is " + maybeNot + "AST.\n"));
            return proof.toString();
        }
    }


    private class NotASTDecidableRNTProof extends Proof.DefaultProof {

        String s;

        public NotASTDecidableRNTProof(String s) {
            super();
            this.s = s;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder proof = new StringBuilder();
            proof.append(o.export("The system is not weakly normalizing since " + s + " does not normalize and can thus trivially not be iAST.\n"));
            proof.append(o.export("We can decide weak reachability because the system is tail-recursive"));
            return proof.toString();
        }
    }

}
