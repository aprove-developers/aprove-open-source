package aprove.verification.probabilistic.Termination.ADPProblem.AST.Processors;

import java.util.*;
import java.util.Map.*;
import java.util.logging.*;

import org.apache.commons.math3.fraction.*;

import aprove.*;
import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.solver.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.Orders.*;
import aprove.verification.dpframework.Orders.SAT.*;
import aprove.verification.dpframework.Orders.Utility.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Logic.*;
import aprove.verification.oldframework.PropositionalLogic.*;
import aprove.verification.oldframework.PropositionalLogic.Formulae.*;
import aprove.verification.oldframework.PropositionalLogic.SATCheckers.*;
import aprove.verification.oldframework.PropositionalLogic.TheoryPropositions.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.ADPProblem.AST.*;
import immutables.*;

/**
 * Subterm Criterion as described in FLOPS24 Invited Journal Paper
 *
 * @author J-C Kassing
 * @version $Id$
 */
public class ADP_AST_SubtermCriterion extends ADP_AST_ProblemProcessor {

    // ================================================================================
    // Properties
    // ================================================================================

    private final static Logger log = Logger.getLogger("aprove.verification.probabilistic.ADPProblem.AST.Processors.AST_ADPSubtermCriterion");

    private final Engine engine;

    // ================================================================================
    // Constructors and Creators
    // ================================================================================

    @ParamsViaArgumentObject
    public ADP_AST_SubtermCriterion(final Arguments arguments) {
        this.engine = arguments.engine;
    }

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isAST_ADPApplicable(final ADP_AST_Problem qdp) {

        if (qdp.isInnermost()) {/**INNERMOST**/
            // No simple projections possible for constants and
            // at most one annotation in each term of each right-hand side
            return ADP_AST_SubtermCriterion.headSymbolsAreAtLeastUnary(qdp)
                && qdp.hasSingleAnnotationInADPs();

        } else {/**FULL and BASIC (non-innermost)**/
            // Not applicable: the subterm criterion is only sound for innermost rewriting;
            // basic start terms do not help, as defined symbols below an annotation may still be created by rules
            return false;
        }
    }

    private static boolean headSymbolsAreAtLeastUnary(final ADP_AST_Problem qdp) {
        for (final FunctionSymbol f : qdp.getDPSymbols()) {
            if (f.getArity() == 0) {
                return false;
            }
        }
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result processAST_ADPProblem(final ADP_AST_Problem oriqAst_ADP, final Abortion aborter) throws AbortionException {
        final Set<Rule> depPairs = oriqAst_ADP.getNonProbDPs();

        long time = System.nanoTime();
        final ImmutableSet<FunctionSymbol> annotatedSyms = oriqAst_ADP.getDPSymbols();
        final SUBEncoder encoder = new SUBEncoder(new FullSharingFlatteningFactory<>(), annotatedSyms, SUB.theSUB);
        aborter.checkAbortion();
        final Formula<None> formula = encoder.encode(depPairs, false, aborter);
        time = System.nanoTime() - time;
        long total = time;
        ADP_AST_SubtermCriterion.log.log(Level.FINER, "Encoding to propositional logic: {0} ms\n", time / 1000000);

        time = System.nanoTime();
        int res[];
        aborter.checkAbortion();
        final SATChecker satChecker = this.engine.getSATChecker();
        try {
            res = satChecker.solve(formula, aborter);
        } catch (final SolverException e) {
            return ResultFactory.unsuccessful();
        }
        time = System.nanoTime() - time;
        total += time;
        ADP_AST_SubtermCriterion.log.log(Level.FINER, "SAT solving: {0} ms\n", time / 1000000);

        if (res != null) {
            time = System.nanoTime();
            final Afs afs = encoder.getAfs(encoder.decode(res, formula.getId()));
            final AfsOrder order = new AfsOrder(afs, SUB.theSUB);
            time = System.nanoTime() - time;
            total += time;
            ADP_AST_SubtermCriterion.log.log(Level.FINER, "Decoding Afs and LPO: {0} ms\n", time / 1000000);
            if (order != null) {
                ADP_AST_SubtermCriterion.log.log(Level.FINE, "Total time: {0} ms\n", total / 1000000);
                return ADP_AST_SubtermCriterion.getResult(order, oriqAst_ADP);
            }

        }
        ADP_AST_SubtermCriterion.log.log(Level.FINE, "Total time: {0} ms\n", total / 1000000);
        return ResultFactory.unsuccessful();
    }

    /**
     * Standard method to compute the result of a subterm processor.
     * @param order
     * @param origqdp
     * @return
     */
    public static Result getResult(final AfsOrder order, final ADP_AST_Problem origqdp)
        throws AbortionException {
        // check which elements of P have been oriented strictly
        Set<ProbabilisticRule> newPRules, deletedPRules;
        newPRules = new LinkedHashSet<>();
        deletedPRules = new LinkedHashSet<>();
        for (final ProbabilisticRule rule : origqdp.getP()) {
            boolean isNonStrict = true;
            for (final Entry<Pair<TRSTerm, BigFraction>, Integer> entry : rule.getRight().getProbabilityMapping().entrySet()) {
                final TRSTerm rhs = entry.getKey().getKey();
                // check if the rule is ordered strictly, i.e.,
                // there exists a term in the rhs that is ordered strictly
                final Set<TRSFunctionApplication> rhsDPsOnlySet = rhs.getAnnoSubterms(origqdp.getDeAnnoMap());

                if (!rhsDPsOnlySet.isEmpty()) {
                    final TRSTerm rhsOnlyDP = rhsDPsOnlySet.iterator().next();
                    if (order.solves(Constraint.fromTerms(rule.getLeft(), rhsOnlyDP, OrderRelation.GR))) {
                        isNonStrict = false;
                    }
                }
            }
            if (isNonStrict) {
                newPRules.add(rule);
            } else {
                deletedPRules.add(rule);
            }
        }

        if (Globals.useAssertions) {
            final ImmutableSet<FunctionSymbol> headSyms = origqdp.getDPSymbols();
            final Afs afs = order.getAfs();
            for (final FunctionSymbol f : afs.getFunctionSymbols()) {
                assert (headSyms.contains(f) && afs.getFiltering(f).y);
            }
            assert (!deletedPRules.isEmpty());
        }

        // build smaller subproblem and proof
        final ADP_AST_Problem newQdp = origqdp.getSubProblem(ImmutableCreator.create(newPRules));
        final Proof proof = new AST_ADPSubtermCriterionProof(deletedPRules, newPRules, order, origqdp, newQdp);
        return ResultFactory.proved(newQdp, YNMImplication.EQUIVALENT, proof);

    }

    // ================================================================================
    // Proof
    // ================================================================================

    static final class AST_ADPSubtermCriterionProof extends QDPProof {

        private final Set<ProbabilisticRule> orientedPRules;
        private final Set<ProbabilisticRule> keptPRules;
        private final ExportableOrder<TRSTerm> order;

        AST_ADPSubtermCriterionProof(final Set<ProbabilisticRule> orientedPRules,
            final Set<ProbabilisticRule> keptPRules,
            final ExportableOrder<TRSTerm> order,
            final ADP_AST_Problem origObl,
            final ADP_AST_Problem resultObl) {
            this.orientedPRules = orientedPRules;
            this.order = order;
            this.keptPRules = keptPRules;
        }

        @Override
        public String export(final Export_Util o, final VerbosityLevel level) {
            StringBuilder result;
            result = new StringBuilder();
            result.append("We use the subterm criterion " + o.cite(Citation.KASSING_DISS) + ".");
            result.append(o.cond_linebreak());
            result.append("The following pairs can be oriented strictly and are deleted.");
            result.append(o.cond_linebreak());
            result.append(o.set(this.orientedPRules, Export_Util.RULES));
            result.append(o.cond_linebreak());
            result.append("The remaining pairs can at least be oriented weakly or contain no annotations.");
            result.append(o.cond_linebreak());
            result.append(o.set(this.keptPRules, Export_Util.RULES));
            result.append(o.cond_linebreak());
            result.append("Used ordering:  ");
            result.append(this.order.export(o));
            result.append(o.cond_linebreak());
            return result.toString();
        }

    }

    // ================================================================================
    // Arguments Class
    // ================================================================================

    public static class Arguments {

        public Engine engine;
    }

}
