package aprove.verification.probabilistic.Termination.PTRSProblem.Processors;

import java.math.*;
import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;

import aprove.prooftree.Export.Utility.*;
import aprove.strategies.Abortions.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;

/**
 * Exact decision procedure for AST of PTRSs in RNT (right-ground, non-overlapping, tail-recursive).
 *
 * The procedure works as follows:
 * <ol>
 * <li>If the PTRS is not ground, it is transformed into a ground PTRS gro(P) in GNT by
 *     instantiating every rule with all instances of its left-hand side that occur in right-hand sides.</li>
 * <li>The ground PTRS is transformed into a stochastic context-free grammar (SCFG) whose
 *     nonterminals are the (ground) left-hand sides. Every right-hand side r is mapped to the word
 *     word(r) of its redexes from left to right.</li>
 * <li>The SCFG is AST iff it is productive (every nonterminal can reach a terminal word) and the
 *     spectral radius of its moment matrix B is at most 1 [EY09, EGK13].</li>
 * <li>The spectral radius condition is decided EXACTLY over the rationals, without any SMT solver:
 *     B is block-triangular w.r.t. the strongly connected components (SCCs) of its graph, so
 *     rho(B) = max over the SCCs D of rho(B_D), where every B_D is irreducible. For an irreducible
 *     non-negative matrix B_D, Gaussian elimination on I - B_D yields
 *     <ul>
 *     <li>rho(B_D) &lt; 1 iff I - B_D is non-singular and the unique solution y of (I - B_D) y = 1 is non-negative
 *         (then y = sum_k B_D^k 1 &gt;= 1),</li>
 *     <li>rho(B_D) = 1 iff I - B_D is singular and its kernel is spanned by a single strictly positive vector
 *         (the Perron vector; the Perron root of an irreducible matrix is simple),</li>
 *     <li>rho(B_D) &gt; 1 otherwise.</li>
 *     </ul>
 *     All three cases are decided with exact rational arithmetic.</li>
 * </ol>
 *
 * @author J-C Kassing
 * @version $Id$
 */
public final class RNTDecisionProcedure {

    private RNTDecisionProcedure() {
    }

    // ================================================================================
    // Applicability
    // ================================================================================

    /**
     * @return true iff R is right-ground, non-overlapping, and tail-recursive.
     */
    public static boolean isRNT(final PTRSProblem R) {
        return R.isRightGround() && R.isNonOverlapping() && R.isTailRecursive();
    }

    /**
     * Used when R is only a part of a larger system, e.g., the ADPs of S in an ADP problem.
     * Then a redex of R in a right-hand side of R behaves as in R only if no other rule can rewrite its arguments.
     *
     * @param R - a PTRS
     * @param rules - all rules that may rewrite the arguments of such a redex (e.g., the rules with active flag)
     * @return true iff in every right-hand side of R, all arguments of subterms with a defined symbol of R at the root
     *         are normal forms w.r.t. rules
     */
    public static boolean argumentsOfRedexesAreNormal(final PTRSProblem R, final Set<ProbabilisticRule> rules) {
        final Set<FunctionSymbol> defs = R.getDefSymbolsOfR();
        for (final ProbabilisticRule rule : R.getPR()) {
            for (final TRSTerm r : rule.getRight().getSupport()) {
                for (final TRSTerm t : r.getSubTerms()) {
                    if (t instanceof TRSFunctionApplication && defs.contains(((TRSFunctionApplication) t).getFunctionSymbol())) {
                        for (final TRSTerm arg : ((TRSFunctionApplication) t).getArguments()) {
                            if (!arg.isNormal(rules)) {
                                return false;
                            }
                        }
                    }
                }
            }
        }
        return true;
    }

    // ================================================================================
    // Decision
    // ================================================================================

    /**
     * Decides AST for a PTRS in RNT.
     * @param R - a PTRS in RNT with a non-empty set of rules
     * @return the verdict together with all intermediate data needed for the proof output
     */
    public static Verdict decide(final PTRSProblem R, final Abortion aborter) throws AbortionException {
        final Verdict v = new Verdict();
        v.originalRules = new ArrayList<>(R.getPR());
        v.ground = R.isGround();

        // Step 1: RNT -> GNT
        if (v.ground) {
            v.groundRules = new ArrayList<>(R.getPR());
        } else {
            v.instantiatedLhss = computeILhs(R.getPR());
            v.groundRules = applyGro(R.getPR(), v.instantiatedLhss);
        }
        aborter.checkAbortion();

        if (v.groundRules.isEmpty()) {
            // no instance of a left-hand side occurs in any right-hand side, i.e., all right-hand sides
            // are normal forms and every rewrite tree has height at most 1
            v.reason = Reason.NO_REDEX_IN_RHS;
            v.ast = true;
            computeRuntimes(v, null, R.getDefSymbolsOfR());
            return v;
        }

        // Step 2: GNT -> SCFG
        v.nonterminals = new ArrayList<>();
        final Map<TRSTerm, Integer> index = new HashMap<>();
        for (final ProbabilisticRule rule : v.groundRules) {
            index.put(rule.getLeft(), v.nonterminals.size());
            v.nonterminals.add(rule.getLeft());
        }
        final int n = v.nonterminals.size();
        v.productions = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            final ProbabilisticRule rule = v.groundRules.get(i);
            for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
                final TRSTerm r = entry.getKey().x;
                final BigFraction p = entry.getKey().y.multiply(entry.getValue());
                final List<Integer> word = new ArrayList<>();
                word(r, index, word);
                v.productions.add(new Production(i, p, r, word));
            }
        }
        aborter.checkAbortion();

        // Step 3: moment matrix (also needed for the reachability analysis of infinite expected runtimes)
        v.moment = new BigFraction[n][n];
        for (int i = 0; i < n; i++) {
            Arrays.fill(v.moment[i], BigFraction.ZERO);
        }
        for (final Production prod : v.productions) {
            for (final int j : prod.word) {
                v.moment[prod.lhs][j] = v.moment[prod.lhs][j].add(prod.probability);
            }
        }

        // Step 4: productivity
        v.productive = new boolean[n];
        boolean changed = true;
        while (changed) {
            changed = false;
            for (final Production prod : v.productions) {
                if (v.productive[prod.lhs]) {
                    continue;
                }
                boolean allProductive = true;
                for (final int j : prod.word) {
                    if (!v.productive[j]) {
                        allProductive = false;
                        break;
                    }
                }
                if (allProductive) {
                    v.productive[prod.lhs] = true;
                    changed = true;
                }
            }
        }
        v.unproductive = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            if (!v.productive[i]) {
                v.unproductive.add(i);
            }
        }
        aborter.checkAbortion();

        // Step 5: exact spectral radius check per SCC (also needed for the expected runtimes if the SCFG is not productive)
        v.sccs = new ArrayList<>();
        boolean allLeqOne = true;
        for (final List<Integer> scc : stronglyConnectedComponents(v.moment)) {
            aborter.checkAbortion();
            final SCCAnalysis analysis = analyzeSCC(v.moment, scc);
            v.sccs.add(analysis);
            if (!analysis.rhoLeqOne()) {
                allLeqOne = false;
            }
        }
        if (!v.unproductive.isEmpty()) {
            v.reason = Reason.UNPRODUCTIVE;
            v.ast = false;
        } else {
            v.reason = Reason.SPECTRAL_RADIUS;
            v.ast = allLeqOne;
        }

        // Step 6: expected runtimes (SAST and runtime bounds)
        computeRuntimes(v, index, R.getDefSymbolsOfR());
        return v;
    }

    // ================================================================================
    // Step 6: expected runtimes
    // ================================================================================

    /**
     * Computes the expected derivation lengths e of the nonterminals (least solution of e = 1 + B e),
     * the expected runtime e_kappa = 1 + sum_{(p:r) in mu} p * e_word(r) of every original rule kappa = l -> mu,
     * and e_max = max_kappa e_kappa. The PTRS is SAST iff e_max is finite.
     *
     * A nonterminal has an infinite expected derivation length iff it is unproductive or it reaches an SCC
     * whose block has spectral radius >= 1. The remaining nonterminals form a set that is closed under
     * reachability whose block has spectral radius < 1, so their expected derivation lengths are the unique
     * solution of the restricted linear system.
     */
    private static void computeRuntimes(final Verdict v, final Map<TRSTerm, Integer> index, final Set<FunctionSymbol> defs) {
        v.ruleRuntimes = new ArrayList<>();
        if (v.reason == Reason.NO_REDEX_IN_RHS) {
            v.sast = true;
            v.eMax = v.originalRules.isEmpty() ? BigFraction.ZERO : BigFraction.ONE;
            for (final ProbabilisticRule rule : v.originalRules) {
                v.ruleRuntimes.add(new RuleRuntime(rule, BigFraction.ONE));
            }
            return;
        }
        final int n = v.nonterminals.size();
        v.infiniteRuntime = new boolean[n];
        for (int i = 0; i < n; i++) {
            v.infiniteRuntime[i] = !v.productive[i];
        }
        for (final SCCAnalysis a : v.sccs) {
            if (!a.rhoLtOne()) {
                for (final int i : a.nodes) {
                    v.infiniteRuntime[i] = true;
                }
            }
        }
        // backward closure: a nonterminal that can create a nonterminal with infinite expected
        // derivation length has an infinite expected derivation length as well
        boolean changed = true;
        while (changed) {
            changed = false;
            for (int i = 0; i < n; i++) {
                if (v.infiniteRuntime[i]) {
                    continue;
                }
                for (int j = 0; j < n; j++) {
                    if (v.infiniteRuntime[j] && v.moment[i][j].compareTo(BigFraction.ZERO) > 0) {
                        v.infiniteRuntime[i] = true;
                        changed = true;
                        break;
                    }
                }
            }
        }
        v.sast = true;
        final List<Integer> finite = new ArrayList<>();
        for (int i = 0; i < n; i++) {
            if (v.infiniteRuntime[i]) {
                v.sast = false;
            } else {
                finite.add(i);
            }
        }
        // solve (I - B_F) e_F = 1 on the finite nonterminals F (closed under reachability, rho(B_F) < 1)
        v.expectedRuntimes = new BigFraction[n];
        final int m = finite.size();
        if (m > 0) {
            final BigFraction[][] aug = new BigFraction[m][m + 1];
            for (int i = 0; i < m; i++) {
                for (int j = 0; j < m; j++) {
                    aug[i][j] = (i == j ? BigFraction.ONE : BigFraction.ZERO).subtract(v.moment[finite.get(i)][finite.get(j)]);
                }
                aug[i][m] = BigFraction.ONE;
            }
            final int[] pivotCols = gaussJordan(aug, m);
            for (int row = 0; row < m; row++) {
                if (pivotCols[row] < 0) {
                    throw new IllegalStateException("I - B is singular on the nonterminals with finite expected runtime");
                }
                v.expectedRuntimes[finite.get(pivotCols[row])] = aug[row][m];
            }
        }
        // expected runtime of every original rule
        v.eMax = null;
        boolean eMaxInfinite = false;
        for (final ProbabilisticRule rule : v.originalRules) {
            BigFraction eKappa = BigFraction.ONE;
            boolean infinite = false;
            for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
                final BigFraction p = entry.getKey().y.multiply(entry.getValue());
                final List<Integer> word = new ArrayList<>();
                word(entry.getKey().x, index, word);
                for (final int j : word) {
                    if (v.infiniteRuntime[j]) {
                        infinite = true;
                    } else {
                        eKappa = eKappa.add(p.multiply(v.expectedRuntimes[j]));
                    }
                }
            }
            v.ruleRuntimes.add(new RuleRuntime(rule, infinite ? null : eKappa));
            if (infinite) {
                eMaxInfinite = true;
            } else if (v.eMax == null || eKappa.compareTo(v.eMax) > 0) {
                v.eMax = eKappa;
            }
        }
        if (eMaxInfinite) {
            v.eMax = null;
        }
        // witness for non-SAST: a basic ground instance of a left-hand side with infinite expected runtime
        // (a ground PTRS may have non-basic left-hand sides like f(g(a)), but the nonterminals of SCCs with
        // rho(B_D) >= 1 and of unproductive productions occur in tail-recursive right-hand sides, so they are basic)
        if (!v.sast) {
            for (int i = 0; i < n; i++) {
                if (v.infiniteRuntime[i] && (v.witnessInstance == null || !isBasic(v.witnessInstance, defs))) {
                    v.witnessInstance = v.nonterminals.get(i);
                }
            }
            for (final ProbabilisticRule rule : v.originalRules) {
                if (rule.getLeft().getMatcher(v.witnessInstance) != null) {
                    v.witnessRule = rule;
                    break;
                }
            }
        }
    }

    /**
     * @return true iff no argument of the ground term t contains a defined symbol
     */
    private static boolean isBasic(final TRSTerm t, final Set<FunctionSymbol> defs) {
        for (final TRSTerm arg : ((TRSFunctionApplication) t).getArguments()) {
            for (final FunctionSymbol f : arg.getFunctionSymbols()) {
                if (defs.contains(f)) {
                    return false;
                }
            }
        }
        return true;
    }

    // ================================================================================
    // Step 1: RNT -> GNT
    // ================================================================================

    /**
     * @return the set ilhs(P) of all subterms of right-hand sides that are instances of a left-hand side
     */
    private static List<TRSTerm> computeILhs(final Set<ProbabilisticRule> rules) {
        final Set<TRSTerm> iLhs = new LinkedHashSet<>();
        for (final ProbabilisticRule rule : rules) {
            for (final TRSTerm rhs : rule.getRight().getSupport()) {
                for (final Pair<Position, TRSTerm> sub : rhs.getPositionsWithSubTerms()) {
                    final TRSTerm subterm = sub.y;
                    if (subterm instanceof TRSVariable) {
                        continue;
                    }
                    for (final ProbabilisticRule rule2 : rules) {
                        // lhs may contain variables, subterm is ground: match lhs onto subterm
                        if (rule2.getLeft().getMatcher(subterm) != null) {
                            iLhs.add(subterm);
                            break; // non-overlapping: at most one rule matches
                        }
                    }
                }
            }
        }
        return new ArrayList<>(iLhs);
    }

    /**
     * @return gro(P) = { l sigma -> mu | l -> mu in P, l sigma in ilhs(P) }
     */
    private static List<ProbabilisticRule> applyGro(final Set<ProbabilisticRule> rules, final List<TRSTerm> iLhs) {
        final List<ProbabilisticRule> newRules = new ArrayList<>();
        for (final TRSTerm inst : iLhs) {
            for (final ProbabilisticRule rule : rules) {
                final TRSSubstitution sigma = rule.getLeft().getMatcher(inst);
                if (sigma != null) {
                    final HashMultiSet<Pair<TRSTerm, BigFraction>> newProbMap = new HashMultiSet<>();
                    for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
                        // right-hand sides are ground, so applying sigma is the identity
                        newProbMap.add(new Pair<>(entry.getKey().x.applySubstitution(sigma), entry.getKey().y), entry.getValue());
                    }
                    newRules.add(ProbabilisticRule.create((TRSFunctionApplication) inst, new MultiDistribution<>(newProbMap)));
                    break; // non-overlapping: at most one rule matches
                }
            }
        }
        return newRules;
    }

    // ================================================================================
    // Step 2: word(t)
    // ================================================================================

    private static void word(final TRSTerm t, final Map<TRSTerm, Integer> index, final List<Integer> word) {
        if (t instanceof TRSVariable) {
            return;
        }
        final Integer i = index.get(t);
        if (i != null) {
            word.add(i);
            return;
        }
        for (final TRSTerm arg : ((TRSFunctionApplication) t).getArguments()) {
            word(arg, index, word);
        }
    }

    // ================================================================================
    // Step 5: SCCs and exact spectral radius check
    // ================================================================================

    /**
     * Tarjan's algorithm on the graph with an edge i -> j iff B[i][j] > 0.
     * @return the SCCs (each sorted ascending) in the order in which they are completed
     */
    static List<List<Integer>> stronglyConnectedComponents(final BigFraction[][] B) {
        final int n = B.length;
        final int[] indexOf = new int[n];
        final int[] lowlink = new int[n];
        final boolean[] onStack = new boolean[n];
        Arrays.fill(indexOf, -1);
        final Deque<Integer> stack = new ArrayDeque<>();
        final List<List<Integer>> result = new ArrayList<>();
        final int[] counter = new int[] { 0 };
        for (int v = 0; v < n; v++) {
            if (indexOf[v] == -1) {
                tarjan(v, B, indexOf, lowlink, onStack, stack, counter, result);
            }
        }
        return result;
    }

    private static void tarjan(final int v,
        final BigFraction[][] B,
        final int[] indexOf,
        final int[] lowlink,
        final boolean[] onStack,
        final Deque<Integer> stack,
        final int[] counter,
        final List<List<Integer>> result) {
        indexOf[v] = counter[0];
        lowlink[v] = counter[0];
        counter[0]++;
        stack.push(v);
        onStack[v] = true;
        for (int w = 0; w < B.length; w++) {
            if (B[v][w].compareTo(BigFraction.ZERO) <= 0) {
                continue;
            }
            if (indexOf[w] == -1) {
                tarjan(w, B, indexOf, lowlink, onStack, stack, counter, result);
                lowlink[v] = Math.min(lowlink[v], lowlink[w]);
            } else if (onStack[w]) {
                lowlink[v] = Math.min(lowlink[v], indexOf[w]);
            }
        }
        if (lowlink[v] == indexOf[v]) {
            final List<Integer> scc = new ArrayList<>();
            int w;
            do {
                w = stack.pop();
                onStack[w] = false;
                scc.add(w);
            } while (w != v);
            Collections.sort(scc);
            result.add(scc);
        }
    }

    /**
     * Decides whether rho(B_D) < 1, = 1, or > 1 for the irreducible block B_D of B given by the SCC D.
     */
    static SCCAnalysis analyzeSCC(final BigFraction[][] B, final List<Integer> scc) {
        final SCCAnalysis a = new SCCAnalysis();
        a.nodes = scc;
        final int m = scc.size();
        a.block = new BigFraction[m][m];
        for (int i = 0; i < m; i++) {
            for (int j = 0; j < m; j++) {
                a.block[i][j] = B[scc.get(i)][scc.get(j)];
            }
        }
        if (m == 1 && a.block[0][0].compareTo(BigFraction.ZERO) == 0) {
            a.kind = SCCKind.TRIVIAL;
            return a;
        }
        // M = I - B_D, augmented with the all-ones vector
        final BigFraction[][] aug = new BigFraction[m][m + 1];
        for (int i = 0; i < m; i++) {
            for (int j = 0; j < m; j++) {
                aug[i][j] = (i == j ? BigFraction.ONE : BigFraction.ZERO).subtract(a.block[i][j]);
            }
            aug[i][m] = BigFraction.ONE;
        }
        final int[] pivotCols = gaussJordan(aug, m);
        int rank = 0;
        for (final int p : pivotCols) {
            if (p >= 0) {
                rank++;
            }
        }
        if (rank == m) {
            // I - B_D is non-singular, so 1 is not an eigenvalue of B_D and rho(B_D) != 1
            a.solution = new BigFraction[m];
            for (int row = 0; row < m; row++) {
                a.solution[pivotCols[row]] = aug[row][m];
            }
            boolean nonNegative = true;
            for (final BigFraction y : a.solution) {
                if (y.compareTo(BigFraction.ZERO) < 0) {
                    nonNegative = false;
                    break;
                }
            }
            a.kind = nonNegative ? SCCKind.RHO_LT_ONE : SCCKind.RHO_GT_ONE_NONSINGULAR;
        } else {
            // 1 is an eigenvalue of B_D, so rho(B_D) >= 1
            a.kernel = kernelBasis(aug, m, pivotCols);
            if (a.kernel.size() == 1) {
                final BigFraction[] v = a.kernel.get(0);
                // normalize the sign such that the first non-zero entry is positive
                int first = 0;
                while (first < m && v[first].compareTo(BigFraction.ZERO) == 0) {
                    first++;
                }
                if (first < m && v[first].compareTo(BigFraction.ZERO) < 0) {
                    for (int i = 0; i < m; i++) {
                        v[i] = v[i].negate();
                    }
                }
                boolean positive = true;
                for (final BigFraction x : v) {
                    if (x.compareTo(BigFraction.ZERO) <= 0) {
                        positive = false;
                        break;
                    }
                }
                a.kind = positive ? SCCKind.RHO_EQ_ONE : SCCKind.RHO_GT_ONE_SINGULAR;
            } else {
                a.kind = SCCKind.RHO_GT_ONE_SINGULAR;
            }
        }
        return a;
    }

    /**
     * Gauss-Jordan elimination (reduced row echelon form) on the first cols columns of aug,
     * carrying all remaining columns along.
     * @return for every row the column of its pivot, or -1 for zero rows
     */
    static int[] gaussJordan(final BigFraction[][] aug, final int cols) {
        final int rows = aug.length;
        final int[] pivotCols = new int[rows];
        Arrays.fill(pivotCols, -1);
        int row = 0;
        for (int col = 0; col < cols && row < rows; col++) {
            int pivot = -1;
            for (int r = row; r < rows; r++) {
                if (aug[r][col].compareTo(BigFraction.ZERO) != 0) {
                    pivot = r;
                    break;
                }
            }
            if (pivot == -1) {
                continue;
            }
            final BigFraction[] tmp = aug[pivot];
            aug[pivot] = aug[row];
            aug[row] = tmp;
            final BigFraction inv = aug[row][col].reciprocal();
            for (int c = 0; c < aug[row].length; c++) {
                aug[row][c] = aug[row][c].multiply(inv);
            }
            for (int r = 0; r < rows; r++) {
                if (r == row) {
                    continue;
                }
                final BigFraction factor = aug[r][col];
                if (factor.compareTo(BigFraction.ZERO) == 0) {
                    continue;
                }
                for (int c = 0; c < aug[r].length; c++) {
                    aug[r][c] = aug[r][c].subtract(factor.multiply(aug[row][c]));
                }
            }
            pivotCols[row] = col;
            row++;
        }
        return pivotCols;
    }

    /**
     * @return a basis of the kernel of the matrix in reduced row echelon form (first cols columns of aug)
     */
    static List<BigFraction[]> kernelBasis(final BigFraction[][] aug, final int cols, final int[] pivotCols) {
        final boolean[] isPivot = new boolean[cols];
        for (final int p : pivotCols) {
            if (p >= 0) {
                isPivot[p] = true;
            }
        }
        final List<BigFraction[]> basis = new ArrayList<>();
        for (int free = 0; free < cols; free++) {
            if (isPivot[free]) {
                continue;
            }
            final BigFraction[] v = new BigFraction[cols];
            Arrays.fill(v, BigFraction.ZERO);
            v[free] = BigFraction.ONE;
            for (int row = 0; row < pivotCols.length; row++) {
                if (pivotCols[row] >= 0) {
                    v[pivotCols[row]] = aug[row][free].negate();
                }
            }
            basis.add(v);
        }
        return basis;
    }

    // ================================================================================
    // Data structures
    // ================================================================================

    public enum Reason {
            /** no instance of a left-hand side occurs in a right-hand side */
            NO_REDEX_IN_RHS,
            /** some nonterminal of the SCFG cannot reach a terminal word */
            UNPRODUCTIVE,
            /** decided by the spectral radius of the moment matrix */
            SPECTRAL_RADIUS
    }

    public enum SCCKind {
            /** single nonterminal without self-loop: rho = 0 */
            TRIVIAL,
            /** I - B_D non-singular with non-negative solution of (I - B_D) y = 1 */
            RHO_LT_ONE,
            /** I - B_D singular with a strictly positive kernel vector (the Perron vector) */
            RHO_EQ_ONE,
            /** I - B_D non-singular, but the solution of (I - B_D) y = 1 has a negative entry */
            RHO_GT_ONE_NONSINGULAR,
            /** I - B_D singular, but the kernel is not spanned by a single strictly positive vector */
            RHO_GT_ONE_SINGULAR
    }

    public static final class Production {

        public final int lhs;
        public final BigFraction probability;
        public final TRSTerm rhs;
        public final List<Integer> word;

        Production(final int lhs, final BigFraction probability, final TRSTerm rhs, final List<Integer> word) {
            this.lhs = lhs;
            this.probability = probability;
            this.rhs = rhs;
            this.word = word;
        }
    }

    /** The expected runtime e_kappa of a rule kappa (null = infinite). */
    public static final class RuleRuntime {

        public final ProbabilisticRule rule;
        public final BigFraction eKappa;

        RuleRuntime(final ProbabilisticRule rule, final BigFraction eKappa) {
            this.rule = rule;
            this.eKappa = eKappa;
        }
    }

    public static final class SCCAnalysis {

        public List<Integer> nodes;
        public BigFraction[][] block;
        public SCCKind kind;
        /** solution y of (I - B_D) y = 1 if I - B_D is non-singular */
        public BigFraction[] solution;
        /** basis of the kernel of I - B_D if it is singular */
        public List<BigFraction[]> kernel;

        public boolean rhoLeqOne() {
            return this.kind == SCCKind.TRIVIAL || this.kind == SCCKind.RHO_LT_ONE || this.kind == SCCKind.RHO_EQ_ONE;
        }

        public boolean rhoLtOne() {
            return this.kind == SCCKind.TRIVIAL || this.kind == SCCKind.RHO_LT_ONE;
        }
    }

    /**
     * The result of the decision procedure together with all data needed to explain it.
     */
    public static final class Verdict {

        public boolean ast;
        public Reason reason;
        public boolean ground;
        public List<ProbabilisticRule> originalRules;
        /** ilhs(P), only if the PTRS was not ground */
        public List<TRSTerm> instantiatedLhss;
        /** the ground PTRS that is transformed into the SCFG (gro(P) or P itself) */
        public List<ProbabilisticRule> groundRules;
        public List<TRSTerm> nonterminals;
        public List<Production> productions;
        public boolean[] productive;
        public List<Integer> unproductive;
        public BigFraction[][] moment;
        public List<SCCAnalysis> sccs;

        /* quantitative part */
        /** true iff the PTRS is SAST, i.e., e_max is finite */
        public boolean sast;
        /** per nonterminal: true iff its expected derivation length is infinite */
        public boolean[] infiniteRuntime;
        /** per nonterminal: its expected derivation length (null if infinite) */
        public BigFraction[] expectedRuntimes;
        /** per original rule kappa: e_kappa = 1 + sum p * e_word(r) (null if infinite) */
        public List<RuleRuntime> ruleRuntimes;
        /** max_kappa e_kappa, or null if infinite */
        public BigFraction eMax;
        /** if not SAST: a ground instance of a left-hand side (a basic term) with infinite expected runtime */
        public TRSTerm witnessInstance;
        /** if not SAST: the rule of the witness instance */
        public ProbabilisticRule witnessRule;

        /**
         * @return the smallest natural number that is >= e_max (only if SAST)
         */
        public BigInteger eMaxCeiling() {
            final BigInteger num = this.eMax.getNumerator();
            final BigInteger den = this.eMax.getDenominator();
            return num.add(den).subtract(BigInteger.ONE).divide(den);
        }

        // ------------------------------------------------------------------------
        // Proof output
        // ------------------------------------------------------------------------

        public String export(final Export_Util o) {
            final StringBuilder s = new StringBuilder();
            s.append(o.export("The PTRS is in RNT (right-ground, non-overlapping, tail-recursive), so we decide AST via a stochastic "
                + "context-free grammar (SCFG) "
                + o.cite(new Citation[] { Citation.EY09, Citation.EGK13 })
                + "."));
            if (!this.ground) {
                s.append(o.export(" We instantiate the rules with ilhs(P) = "));
                s.append(o.set(this.instantiatedLhss, Export_Util.SIMPLESET));
                s.append(o.export(", which yields a ground PTRS gro(P) that is AST iff the PTRS is AST."));
            }
            s.append(o.paragraph());

            if (this.reason == Reason.NO_REDEX_IN_RHS) {
                s.append(o.export("No instance of a left-hand side occurs in a right-hand side, so every rewrite tree has at most one step "
                    + "and the PTRS is AST."));
                return s.toString();
            }

            // SCFG
            s.append(o.export("The SCFG has a nonterminal for every left-hand side of " + (this.ground ? "the PTRS" : "gro(P)")
                + " and maps every right-hand side to the word of its redexes:"));
            s.append(o.linebreak());
            for (int i = 0; i < this.nonterminals.size(); i++) {
                s.append(o.export("  N" + (i + 1) + " = " + this.nonterminals.get(i).toString()));
                s.append(o.linebreak());
            }
            for (final Production prod : this.productions) {
                final StringBuilder w = new StringBuilder();
                if (prod.word.isEmpty()) {
                    w.append("epsilon");
                } else {
                    for (final int j : prod.word) {
                        if (w.length() > 0) {
                            w.append(' ');
                        }
                        w.append('N').append(j + 1);
                    }
                }
                s.append(o.export("  N" + (prod.lhs + 1) + " -> " + prod.probability + " : " + w + "    (from " + prod.rhs + ")"));
                s.append(o.linebreak());
            }
            s.append(o.paragraph());

            // productivity
            if (this.reason == Reason.UNPRODUCTIVE) {
                s.append(o.export("The nonterminal(s) " + names(this.unproductive)
                    + " cannot reach a terminal word, so the PTRS is not AST."));
                return s.toString();
            }

            // moment matrix and spectral radius
            s.append(o.export("The SCFG is productive and has the moment matrix B:"));
            s.append(o.linebreak());
            s.append(exportMatrix(o, this.moment, null));
            s.append(o.export("By " + o.cite(new Citation[] { Citation.EY09, Citation.EGK13 })
                + ", it is AST iff rho(B) <= 1, where rho(B) is the maximum of rho(B_D) "
                + "over all SCCs D of B:"));
            s.append(o.linebreak());
            for (final SCCAnalysis a : this.sccs) {
                final String d = "  {" + names(a.nodes) + "}: ";
                switch (a.kind) {
                    case TRIVIAL -> s.append(o.export(d + "no self-loop, so rho(B_D) = 0."));
                    case RHO_LT_ONE -> s.append(o.export(d + "(I - B_D) y = 1 has the non-negative solution y = "
                        + vectorToString(a.solution)
                        + ", so rho(B_D) < 1."));
                    case RHO_GT_ONE_NONSINGULAR -> s.append(o.export(d + "the solution y = "
                        + vectorToString(a.solution)
                        + " of (I - B_D) y = 1 has a negative entry, so rho(B_D) > 1."));
                    case RHO_EQ_ONE -> s.append(o.export(d + "I - B_D is singular with the strictly positive kernel vector v = "
                        + vectorToString(a.kernel.get(0))
                        + ", so rho(B_D) = 1."));
                    case RHO_GT_ONE_SINGULAR -> {
                        if (a.kernel.size() == 1) {
                            s.append(o.export(d + "I - B_D is singular, but its kernel vector v = "
                                + vectorToString(a.kernel.get(0))
                                + " is not strictly positive, so rho(B_D) > 1."));
                        } else {
                            s.append(o.export(d + "I - B_D is singular with a kernel of dimension "
                                + a.kernel.size()
                                + " > 1, so rho(B_D) > 1."));
                        }
                    }
                    default -> {
                    }
                }
                s.append(o.linebreak());
            }
            s.append(o.export(this.ast ? "Hence, rho(B) <= 1 and the PTRS is AST." : "Hence, rho(B) > 1 and the PTRS is not AST."));
            return s.toString();
        }

        /**
         * Proof text for the quantitative part (expected runtimes, SAST). To be used after {@link #export(Export_Util)}.
         */
        public String exportRuntime(final Export_Util o) {
            final StringBuilder s = new StringBuilder();
            if (this.reason == Reason.NO_REDEX_IN_RHS) {
                s.append(o.export("As all right-hand sides are normal forms, e_max = " + this.eMax
                    + ", so the PTRS is SAST and every term t "
                    + "has an expected runtime of at most e_max * |pos_D(t)|."));
                return s.toString();
            }
            if (this.sast) {
                s.append(o.export("As rho(B) < 1, the expected derivation lengths e = (I - B)^-1 1 of the nonterminals are:"));
                s.append(o.linebreak());
            } else {
                final List<Integer> inf = new ArrayList<>();
                for (int i = 0; i < this.nonterminals.size(); i++) {
                    if (this.infiniteRuntime[i]) {
                        inf.add(i);
                    }
                }
                s.append(o.export("The nonterminal(s) " + names(inf)
                    + " have an infinite expected derivation length (they are "
                    + "unproductive or reach an SCC with rho(B_D) >= 1)"
                    + (inf.size() < this.nonterminals.size() ? ", the others have:" : ".")));
                s.append(o.linebreak());
            }
            for (int i = 0; i < this.nonterminals.size(); i++) {
                if (!this.infiniteRuntime[i]) {
                    s.append(o.export("  e(N" + (i + 1) + ") = " + this.expectedRuntimes[i]));
                    s.append(o.linebreak());
                }
            }
            s.append(o.export("So a redex of a rule kappa = l -> mu has the expected runtime e_kappa = 1 + sum_{(p:r) in mu} p * e(word(r)):"));
            s.append(o.linebreak());
            for (final RuleRuntime rr : this.ruleRuntimes) {
                s.append(o.export("  " + rr.rule.getLeft() + ": e_kappa = " + (rr.eKappa == null ? "infinity" : rr.eKappa.toString())));
                s.append(o.linebreak());
            }
            if (this.sast) {
                s.append(o.export("Hence, e_max = " + this.eMax
                    + ", so the PTRS is SAST and every term t has an expected runtime of "
                    + "at most e_max * |pos_D(t)|."));
            } else {
                s.append(o.export("Hence, the PTRS is not SAST: the basic term " + this.witnessInstance
                    + " (an instance of "
                    + this.witnessRule.getLeft()
                    + ") has an infinite expected runtime."));
            }
            return s.toString();
        }

        private static String names(final Collection<Integer> nodes) {
            final StringBuilder s = new StringBuilder();
            for (final int i : nodes) {
                if (s.length() > 0) {
                    s.append(", ");
                }
                s.append('N').append(i + 1);
            }
            return s.toString();
        }

        private static String vectorToString(final BigFraction[] v) {
            final StringBuilder s = new StringBuilder("(");
            for (int i = 0; i < v.length; i++) {
                if (i > 0) {
                    s.append(", ");
                }
                s.append(v[i]);
            }
            return s.append(')').toString();
        }

        private static String exportMatrix(final Export_Util o, final BigFraction[][] m, final List<Integer> labels) {
            final StringBuilder s = new StringBuilder();
            int width = 1;
            for (final BigFraction[] row : m) {
                for (final BigFraction x : row) {
                    width = Math.max(width, x.toString().length());
                }
            }
            for (final BigFraction[] row : m) {
                final StringBuilder line = new StringBuilder("  [");
                for (int j = 0; j < row.length; j++) {
                    final String x = row[j].toString();
                    if (j > 0) {
                        line.append("  ");
                    }
                    for (int pad = x.length(); pad < width; pad++) {
                        line.append(' ');
                    }
                    line.append(x);
                }
                line.append(']');
                s.append(o.export(line.toString()));
                s.append(o.linebreak());
            }
            return s.toString();
        }
    }
}
