package aprove.verification.probabilistic.Complexity.PTRSProblem.Processors;

import java.util.*;

import aprove.*;
import aprove.cli.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.prooftree.Proofs.Proof.*;
import aprove.runtime.*;
import aprove.strategies.Abortions.*;
import aprove.verification.complexity.Implications.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Complexity.PTRSProblem.*;
import immutables.*;

/**
 * Processor to convert DerivationalComplexityProblem R/S to an
 * instrumented RuntimeComplexityProblem R'/S' where
 * either R' = R and S' \supseteq S and rc(R'/S') = dc(R/S),
 * or R' \supset R and S' = S and rc(R'/S') = max(O(n), dc(R/S)).
 *
 * @author J-C Kassing
 */
public class PTRS_Cpx_DerivationalToRuntimeProcessor extends PTRS_Cpx_Processor {

    /** The default name for the function symbol of the function that
     *  does the actual conversion of the arguments via rewrite rules.
     */
    private static final String CONVERT_SYMBOL_NAME = "encArg";

    /** The default suffix for the function symbol of the function that
     *  does the actual conversion of the root via rewrite rules.
     */
    private static final String ENCODE_SYMBOL_PREFIX = "encode";

    /** The default suffix for the constructor symbols representing the
     *  defined symbols.
     */
    private static final String CONS_SYMBOL_PREFIX = "cons";

    /** Prefix for the name of fresh variables. */
    private static final String VAR_PREFIX = "x_";

    /**
     * @param rules the rules for which we want to generate the encoding rules
     * @return the encoding rules
     */
    private static LinkedHashSet<ProbabilisticRule> generateEncodingRulesForRules(final Set<Rule> rules) {
        final Set<FunctionSymbol> allSyms = CollectionUtils.getFunctionSymbols(rules);
        final Set<FunctionSymbol> definedSyms = CollectionUtils.getRootSymbols(rules);
        final Set<FunctionSymbol> constructorSyms = new LinkedHashSet<>();
        for (final FunctionSymbol f : allSyms) {
            if (!definedSyms.contains(f)) {
                constructorSyms.add(f);
            }
        }
        final int maxArity = CollectionUtils.getMaxArity(allSyms);
        return generateEncodingRulesForSyms(allSyms, definedSyms, constructorSyms, maxArity);
    }

    /**
     * Generate rules expressing the conversion from basic terms over an
     * extended signature to arbitrary terms over the original signature.
     *
     * @param allSyms the union of definedSyms and constructorSyms; non-null
     * @param definedSyms to be treated like defined symbols by the conversion;
     *  non-null
     * @param constructorSyms to be treated like constructor symbols by the
     *  conversion; non-null
     * @param maxArity the maximum arity of the FunctionSymbols in allSyms
     * @return rules encoding the conversion from basic terms over an extended
     *  signature to arbitrary terms over the original signature
     */
    private static LinkedHashSet<ProbabilisticRule> generateEncodingRulesForSyms(final Set<FunctionSymbol> allSyms,
        final Set<FunctionSymbol> definedSyms,
        final Set<FunctionSymbol> constructorSyms,
        final int maxArity) {
        final LinkedHashSet<ProbabilisticRule> result = new LinkedHashSet<>();

        // fresh name generation infrastructure
        final Set<String> used = CollectionUtils.getNames(definedSyms);
        used.addAll(CollectionUtils.getNames(constructorSyms));
        final FreshNameGenerator fridge = new FreshNameGenerator(used, FreshNameGenerator.APPEND_NUMBERS);
        // make unary converter symbol (let's call it 'conv')
        final String freshConvName = fridge.getFreshName(CONVERT_SYMBOL_NAME, false);
        fridge.lockName(freshConvName);
        final FunctionSymbol fConv = FunctionSymbol.create(freshConvName, 1);

        // make fresh vars for rules
        final List<TRSVariable> vars = makeVars(fridge, maxArity);

        // for constructor symbols f: make conv(f(x_1, ..., x_n)) -> f(conv(x_1), ..., conv(x_n))
        for (final FunctionSymbol f : constructorSyms) {
            final Rule rule = encodeConvRule(fConv, f, f, vars);
            final ProbabilisticRule probRule = ProbabilisticRule.create(rule.getLeft(), rule.getRight());
            result.add(probRule);
        }

        // for defined symbols f: make conv(cons_f(x_1, ..., x_n)) -> f(conv(x_1), ..., conv(x_n))
        for (final FunctionSymbol f : definedSyms) {
            final String freshName = fridge.getFreshName(CONS_SYMBOL_PREFIX + "_" + f.getName(), false);
            fridge.lockName(freshName);
            final FunctionSymbol fCons = FunctionSymbol.create(freshName, f.getArity());
            final Rule argConvRule = encodeConvRule(fConv, fCons, f, vars);
            final ProbabilisticRule probRule = ProbabilisticRule.create(argConvRule.getLeft(), argConvRule.getRight());
            result.add(probRule);
        }

        // for all symbols f: make enc_f(x_1, ..., x_n) -> f(conv(x_1), ..., conv(x_n))
        for (final FunctionSymbol f : allSyms) {
            final String freshEncName = fridge.getFreshName(ENCODE_SYMBOL_PREFIX + "_" + f.getName(), false);
            fridge.lockName(freshEncName);
            final FunctionSymbol fEnc = FunctionSymbol.create(freshEncName, f.getArity());
            final Rule encRule = encodeEncRule(fEnc, f, fConv, vars);
            final ProbabilisticRule probRule = ProbabilisticRule.create(encRule.getLeft(), encRule.getRight());
            result.add(probRule);
        }

        return result;
    }

    /**
     * Returns fConv(leftSym(x_1, ..., x_n)) -> rightSym(fConv(x_1), ..., fConv(x_n)).
     * @param fConv non-null
     * @param leftSym non-null
     * @param rightSym non-null
     * @param vars [x_1, ..., x_maxArity]
     * @return fConv(leftSym(x_1, ..., x_n)) -> rightSym(fConv(x_1), ..., fConv(x_n))
     */
    private static Rule encodeConvRule(final FunctionSymbol fConv,
        final FunctionSymbol leftSym,
        final FunctionSymbol rightSym,
        final List<TRSVariable> vars) {
        final int arity = leftSym.getArity();
        if (Globals.useAssertions) {
            assert arity == rightSym.getArity();
        }

        // goal: build rule   lhs -> rhs
        // lhs = fConv(leftSym(x_1, ..., x_n))
        final ArrayList<TRSVariable> argVars = new ArrayList<>(vars.subList(0, arity));
        final ImmutableList<TRSVariable> argVarsImm = ImmutableCreator.create(argVars);
        final TRSTerm leftSymApp = TRSTerm.createFunctionApplication(leftSym, argVarsImm);
        final TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(fConv, leftSymApp);

        // rhs = rightSym(fConv(x_1), ..., fConv(x_n))
        final ArrayList<TRSFunctionApplication> rhsArgs = new ArrayList<>(arity);
        for (int i = 0; i < arity; ++i) {
            final TRSVariable v = vars.get(i);
            final TRSFunctionApplication fConvV = TRSTerm.createFunctionApplication(fConv, v);
            rhsArgs.add(fConvV);
        }
        final ImmutableList<TRSFunctionApplication> rhsArgsImm = ImmutableCreator.create(rhsArgs);
        final TRSFunctionApplication rhs = TRSTerm.createFunctionApplication(rightSym, rhsArgsImm);
        return Rule.create(lhs, rhs);
    }

    /**
     * Returns fEnc(x_1, ..., x_n) -> rightSym(argConv(x_1), ..., argConv(x_n)).
     * @param fEnc non-null
     * @param rightSym non-null
     * @param argConv non-null
     * @param vars [x_1, ..., x_maxArity]
     * @return fEnc(x_1, ..., x_n) -> rightSym(argConv(x_1), ..., argConv(x_n))
     */
    private static Rule encodeEncRule(final FunctionSymbol fEnc,
        final FunctionSymbol rightSym,
        final FunctionSymbol argConv,
        final List<TRSVariable> vars) {
        final int arity = fEnc.getArity();
        if (Globals.useAssertions) {
            assert arity == rightSym.getArity();
        }

        // goal: build rule   lhs -> rhs
        // lhs = fEnc(x_1, ..., x_n))
        final ArrayList<TRSVariable> argVars = new ArrayList<>(vars.subList(0, arity));
        final ImmutableList<TRSVariable> argVarsImm = ImmutableCreator.create(argVars);
        final TRSFunctionApplication lhs = TRSTerm.createFunctionApplication(fEnc, argVarsImm);

        // rhs = rightSym(fConv(x_1), ..., fConv(x_n))
        final ArrayList<TRSFunctionApplication> rhsArgs = new ArrayList<>(arity);
        for (int i = 0; i < arity; ++i) {
            final TRSVariable v = vars.get(i);
            final TRSFunctionApplication fConvV = TRSTerm.createFunctionApplication(argConv, v);
            rhsArgs.add(fConvV);
        }
        final ImmutableList<TRSFunctionApplication> rhsArgsImm = ImmutableCreator.create(rhsArgs);
        final TRSFunctionApplication rhs = TRSTerm.createFunctionApplication(rightSym, rhsArgsImm);
        return Rule.create(lhs, rhs);
    }

    /**
     * Returns a list of distinct fresh variables, with length howMany.
     * Side effect: fridge will no longer consider the names of the new
     * variables as fresh.
     *
     * @param fridge generates names for variables, non-null
     * @param howMany number of fresh variables to generate
     * @return a list of distinct fresh variables, with length howMany
     */
    private static ArrayList<TRSVariable> makeVars(final FreshNameGenerator fridge, final int howMany) {
        final ArrayList<TRSVariable> res = new ArrayList<>(howMany);
        for (int i = 0; i < howMany; ++i) {
            final String proposedName = VAR_PREFIX + (i + 1);
            final String freshName = fridge.getFreshName(proposedName, false);
            fridge.lockName(freshName);
            final TRSVariable var = TRSTerm.createVariable(freshName);
            res.add(var);
        }
        return res;
    }

    private class CpxPTRS_DerivationToRuntimeComplexityProof extends DefaultProof {

        private Set<ProbabilisticRule> newRules;

        private CpxPTRS_DerivationToRuntimeComplexityProof(final Set<ProbabilisticRule> newRules) {
            this.newRules = newRules;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            final StringBuilder result = new StringBuilder();
            result.append("The following rules have been added to R to convert the given derivational complexity problem to a runtime complexity problem "
                + o.cite(Citation.KASSING_DISS) + ":");
            result.append(o.cond_linebreak());
            result.append(o.set(this.newRules, Export_Util.RULES));
            result.append(o.cond_linebreak());
            return result.toString();
        }
    }

    public static class Arguments {

        public boolean introRelativeRules = true;
    }

    @Override
    protected boolean isCpxPTRSApplicable(final PTRS_Cpx_Problem obl) {
        return !obl.isBasic() && Options.certifier == Certifier.NONE;
    }

    @Override
    protected Result processCpxPTRS(final PTRS_Cpx_Problem cpxTrs, final Abortion aborter) throws AbortionException {
        final ImmutableSet<Rule> nonProbAbstractionRules = ImmutableCreator.create(cpxTrs.getNonProbAbstraction().getR());

        final Set<ProbabilisticRule> encodingRules = generateEncodingRulesForRules(nonProbAbstractionRules);
        ImmutableSet<ProbabilisticRule> newPR;
        final Set<ProbabilisticRule> protoNewR = new LinkedHashSet<>();
        protoNewR.addAll(encodingRules);
        protoNewR.addAll(cpxTrs.getPR());
        newPR = ImmutableCreator.create(protoNewR);
        final PTRS_Cpx_Problem newBobl = PTRS_Cpx_Problem.create(newPR, cpxTrs.getRewriteStrategy(), true);
        final Proof proof = new CpxPTRS_DerivationToRuntimeComplexityProof(encodingRules);
        return ResultFactory.proved(newBobl, SoundUpperUnsoundLowerBound.create(), proof);
    }
}
