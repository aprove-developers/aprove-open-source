package aprove.verification.probabilistic.BasicStructures;

import java.util.*;
import java.util.Map.*;

import org.apache.commons.math3.fraction.*;

import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import immutables.*;

/**
 * Implements the transformation from outermost to innermost rewriting for PTRSs, i.e., the
 * transformation {@code Trans_o} of Kassing's dissertation
 * (Section "From Outermost to Innermost Evaluation", adapting Thiemann's transformation
 * [thiemann_outermost_2009] to the probabilistic setting).
 * <p>
 * Given a PTRS {@code P} over a signature {@code Sigma}, we build a new PTRS {@code Trans_o(P)}
 * over the extended signature
 * {@code Sigma' = Sigma + {op, reduce, goUp, result} + {check_f, redex_f, in_{f,i} | f in Sigma, 1 <= i <= arity(f)}}
 * such that innermost AST of {@code Trans_o(P)} implies outermost AST of {@code P}.
 * An outermost step is simulated in three phases: {@code reduce} descends to the root of an
 * outermost redex, {@code redex_f} performs the actual step, and {@code goUp} moves the marker
 * back to the root (where {@code op} restarts the search). The innermost strategy guarantees that
 * a {@code redex_f(...)} subterm is only left in favour of descending further ({@code check_f -> in_{f,i}})
 * when it is a normal form, i.e., when the root is not a redex -- exactly the outermost condition.
 *
 * @author J-C Kassing
 */
public final class OutermostToInnermostTransformation {

    private static final String OP_NAME = "op";
    private static final String REDUCE_NAME = "reduce";
    private static final String GOUP_NAME = "goUp";
    private static final String RESULT_NAME = "result";
    private static final String CHECK_PREFIX = "check_";
    private static final String REDEX_PREFIX = "redex_";
    private static final String IN_PREFIX = "in_";
    private static final String VAR_PREFIX = "x_";

    private OutermostToInnermostTransformation() {
        // utility class
    }

    /**
     * The fresh marker symbols {@code op, reduce, goUp, result} introduced by the transformation.
     * {@code op} marks the root of the original term and is meant to wrap the start term as
     * {@code op(reduce(t))}; the others track the current reduction position.
     */
    public static final class Markers {

        public final FunctionSymbol op;
        public final FunctionSymbol reduce;
        public final FunctionSymbol goUp;
        public final FunctionSymbol result;

        private Markers(final FunctionSymbol op, final FunctionSymbol reduce, final FunctionSymbol goUp, final FunctionSymbol result) {
            this.op = op;
            this.reduce = reduce;
            this.goUp = goUp;
            this.result = result;
        }
    }

    /**
     * The result of the transformation: the rules of {@code Trans_o(P)} together with the fresh
     * marker symbols (so that callers can, e.g., form the intended start term {@code op(reduce(t))}).
     */
    public static final class Result {

        public final ImmutableSet<ProbabilisticRule> rules;
        public final Markers markers;

        private Result(final ImmutableSet<ProbabilisticRule> rules, final Markers markers) {
            this.rules = rules;
            this.markers = markers;
        }
    }

    /**
     * Builds {@code Trans_o(P)} for the given PTRS.
     *
     * @param originalRules the probabilistic rules of the original PTRS {@code P}
     * @param signature the signature {@code Sigma} of {@code P}, i.e., all function symbols occurring in it
     * @return the rules of {@code Trans_o(P)} and the fresh marker symbols
     */
    public static Result transform(final Set<ProbabilisticRule> originalRules, final Collection<FunctionSymbol> signature) {
        // Deterministic order over the signature.
        final List<FunctionSymbol> syms = new ArrayList<>(signature);

        // Fresh name generation, seeded with the existing function symbol names.
        final Set<String> used = new LinkedHashSet<>(CollectionUtils.getNames(new LinkedHashSet<>(signature)));
        final FreshNameGenerator fridge = new FreshNameGenerator(used, FreshNameGenerator.APPEND_NUMBERS);

        final FunctionSymbol opSym = freshSymbol(fridge, OP_NAME, 1);
        final FunctionSymbol reduceSym = freshSymbol(fridge, REDUCE_NAME, 1);
        final FunctionSymbol goUpSym = freshSymbol(fridge, GOUP_NAME, 1);
        final FunctionSymbol resultSym = freshSymbol(fridge, RESULT_NAME, 1);

        // Per-symbol markers check_f (arity 1), redex_f (arity m), in_{f,i} (arity m).
        final Map<FunctionSymbol, FunctionSymbol> checkOf = new LinkedHashMap<>();
        final Map<FunctionSymbol, FunctionSymbol> redexOf = new LinkedHashMap<>();
        final Map<FunctionSymbol, List<FunctionSymbol>> inOf = new LinkedHashMap<>();
        int maxArity = 1; // at least 1 for the unary marker rules
        for (final FunctionSymbol f : syms) {
            final int m = f.getArity();
            maxArity = Math.max(maxArity, m);
            checkOf.put(f, freshSymbol(fridge, CHECK_PREFIX + f.getName(), 1));
            redexOf.put(f, freshSymbol(fridge, REDEX_PREFIX + f.getName(), m));
            final List<FunctionSymbol> ins = new ArrayList<>(m);
            for (int i = 0; i < m; i++) {
                ins.add(freshSymbol(fridge, IN_PREFIX + f.getName() + "_" + (i + 1), m));
            }
            inOf.put(f, ins);
        }

        // Fresh variables x_1, ..., x_maxArity (reused per rule; rules have independent scopes).
        final List<TRSVariable> vars = new ArrayList<>(maxArity);
        for (int i = 0; i < maxArity; i++) {
            vars.add(TRSTerm.createVariable(fridge.getFreshName(VAR_PREFIX + (i + 1), false)));
        }

        final LinkedHashSet<ProbabilisticRule> rules = new LinkedHashSet<>();

        for (final FunctionSymbol f : syms) {
            final int m = f.getArity();
            final FunctionSymbol checkF = checkOf.get(f);
            final FunctionSymbol redexF = redexOf.get(f);
            final List<FunctionSymbol> ins = inOf.get(f);
            final ImmutableList<TRSVariable> argVars = ImmutableCreator.create(new ArrayList<>(vars.subList(0, m)));

            // (1)  reduce(f(x_1, ..., x_m)) -> { 1 : check_f(redex_f(x_1, ..., x_m)) }
            final TRSFunctionApplication fApp = TRSTerm.createFunctionApplication(f, argVars);
            final TRSFunctionApplication redexApp = TRSTerm.createFunctionApplication(redexF, argVars);
            rules.add(ProbabilisticRule.create(
                TRSTerm.createFunctionApplication(reduceSym, fApp),
                TRSTerm.createFunctionApplication(checkF, redexApp)));

            // (2)  check_f(redex_f(x_1, ..., x_m)) -> { 1 : in_{f,i}(x_1, ..., reduce(x_i), ..., x_m) }
            for (int i = 0; i < m; i++) {
                final List<TRSTerm> inArgs = new ArrayList<>(argVars);
                inArgs.set(i, TRSTerm.createFunctionApplication(reduceSym, vars.get(i)));
                rules.add(ProbabilisticRule.create(
                    TRSTerm.createFunctionApplication(checkF, redexApp),
                    TRSTerm.createFunctionApplication(ins.get(i), ImmutableCreator.create(inArgs))));
            }

            // (4)  check_f(result(x_1)) -> { 1 : goUp(x_1) }
            rules.add(ProbabilisticRule.create(
                TRSTerm.createFunctionApplication(checkF, TRSTerm.createFunctionApplication(resultSym, vars.get(0))),
                TRSTerm.createFunctionApplication(goUpSym, vars.get(0))));

            // (5)  in_{f,i}(x_1, ..., goUp(x_i), ..., x_m) -> { 1 : goUp(f(x_1, ..., x_m)) }
            for (int i = 0; i < m; i++) {
                final List<TRSTerm> inArgs = new ArrayList<>(argVars);
                inArgs.set(i, TRSTerm.createFunctionApplication(goUpSym, vars.get(i)));
                rules.add(ProbabilisticRule.create(
                    TRSTerm.createFunctionApplication(ins.get(i), ImmutableCreator.create(inArgs)),
                    TRSTerm.createFunctionApplication(goUpSym, TRSTerm.createFunctionApplication(f, argVars))));
            }
        }

        // (3)  redex_f(l_1, ..., l_m) -> { p_1 : result(r_1), ..., p_k : result(r_k) }   for each original rule
        for (final ProbabilisticRule rule : originalRules) {
            final TRSFunctionApplication left = rule.getLeft();
            final FunctionSymbol f = left.getRootSymbol();
            final FunctionSymbol redexF = redexOf.get(f);
            final TRSFunctionApplication redexLeft = TRSTerm.createFunctionApplication(redexF, left.getArguments());

            final MultiDistribution.Builder<TRSTerm> builder = new MultiDistribution.Builder<>();
            for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
                final TRSTerm rhs = entry.getKey().getKey();
                final BigFraction prob = entry.getKey().getValue();
                final TRSTerm wrapped = TRSTerm.createFunctionApplication(resultSym, rhs);
                for (int c = 0; c < entry.getValue(); c++) {
                    builder.add(wrapped, prob);
                }
            }
            rules.add(ProbabilisticRule.create(redexLeft, builder.build()));
        }

        // (6)  op(goUp(x_1)) -> { 1 : op(reduce(x_1)) }
        rules.add(ProbabilisticRule.create(
            TRSTerm.createFunctionApplication(opSym, TRSTerm.createFunctionApplication(goUpSym, vars.get(0))),
            TRSTerm.createFunctionApplication(opSym, TRSTerm.createFunctionApplication(reduceSym, vars.get(0)))));

        return new Result(ImmutableCreator.create(rules), new Markers(opSym, reduceSym, goUpSym, resultSym));
    }

    private static FunctionSymbol freshSymbol(final FreshNameGenerator fridge, final String proposedName, final int arity) {
        final String name = fridge.getFreshName(proposedName, false);
        fridge.lockName(name);
        return FunctionSymbol.create(name, arity);
    }
}
