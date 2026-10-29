package aprove.input.Programs.ariTrs;

import java.util.*;
import java.util.Map.*;

import aprove.input.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.complexity.CpxGTrsProblem.*;
import aprove.verification.complexity.CpxRelTrsProblem.*;
import aprove.verification.complexity.CpxTrsProblem.*;
import aprove.verification.confluence.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Complexity.PTRSProblem.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import immutables.*;

/**
 * @author Jan-Christoph Kassing
 * The ObligationCreator for all types of probabilistic TRS.
 * Similar to the ObligationCreator of non-probabilistic TRS but with less options (as of now).
 */
public class ObligationCreator {

    /*
     * Every possible valid information of the input is coded
     * into a number to the power of 2, so the sum of every
     * valid combination is exactly one integer value.
     */
    private final static int bitEquational = 1 << 1;
    private final static int bitRelativeRules = 1 << 2;
    private final static int bitConditionalRules = 1 << 3;
    private final static int bitContextSensitiveRules = 1 << 4;
    private final static int bitInnermost = 1 << 5;
    private final static int bitOutermost = 1 << 6;
    private final static int bitGeneralizedRules = 1 << 7;
    private final static int bitComplexity = 1 << 8;
    private final static int bitConstructorbased = 1 << 9;
    private final static int bitParallelInnermost = 1 << 10;
    private final static int bitProbabilistic = 1 << 11;
    private final static int bitTermination = 1 << 12;
    private final static int bitAST = 1 << 13;
    private final static int bitSAST = 1 << 14;    
    private final static int bitConfluence = 1 << 15;
    private final static int bitInfeasibility = 1 << 16;

    private static boolean notEmpty(final Collection<?> c) {
        return c != null && !c.isEmpty();
    }
    
    /*
     * Declaration of the Constructs to which the parser will
     * collect information.
     */
    private Set<FunctionSymbol> assAndComFunctionSymbols;
    private Set<FunctionSymbol> associativeFunctionSymbols;
    private Set<FunctionSymbol> commutativeFunctionSymbols;
    
    private boolean complexity;
    
    private Set<ConditionalRule> conditionalRules;
    
    private HashMap<FunctionSymbol, Set<Integer>> replacementMap;
    
    private Set<Equation> equations;
    
    private Set<GeneralizedRule> allRules;
    private Set<Rule> relativeRules;
    private Set<Rule> simpleRules;
    private Set<Pair<TRSTerm,TRSTerm>> lhsVariableRelRules;
    private boolean innermost;
    private Language language = null;
    private final List<ParseError> obligationErrors;
    private boolean outermost;
    private boolean parallelInnermost;

    private boolean probabilistic;
    private boolean termination;
    private boolean ast;
    private boolean sast;
    private boolean basic;
    private Set<ProbabilisticRule> probabilisticRules;
    
    private boolean confluence;
    private boolean infeasibility;
    private Set<Condition> infeasibilityQuery;

    public ObligationCreator(final RawAriTrs rawptrs) {
        this.obligationErrors = new LinkedList<ParseError>();
        this.getAll(rawptrs);
    }

    public BasicObligation buildObligation() throws ObligationCreatorException {
        final BasicObligation obligation = this.generateProblem();
        if (!this.obligationErrors.isEmpty()) {
            throw new ObligationCreatorException(this.obligationErrors);
        } else {
            return obligation;
        }
    }

    public List<ParseError> getErrors() {
        return this.obligationErrors;
    }

    public Language getLanguage() {
        return this.language;
    }
    
    private Set<Equation> computeEquations() {
        final Set<FunctionSymbol> FuncSymbolsOfSimpleRules = CollectionUtils.getFunctionSymbols(this.simpleRules);
        final Set<Equation> result = new LinkedHashSet<Equation>();
        if (this.equations != null) {
            result.addAll(this.equations);
        }
        if (ObligationCreator.notEmpty(this.commutativeFunctionSymbols)) {
            result.addAll(OblCreatorEtrs.getCommutativeEquations(
                OblCreatorEtrs.buildSymColl(this.commutativeFunctionSymbols), FuncSymbolsOfSimpleRules));
        }
        if (ObligationCreator.notEmpty(this.associativeFunctionSymbols)) {
            result.addAll(OblCreatorEtrs.getAssociativeEquations(
                OblCreatorEtrs.buildSymColl(this.associativeFunctionSymbols), FuncSymbolsOfSimpleRules));
        }
        if (ObligationCreator.notEmpty(this.assAndComFunctionSymbols)) {
            final Set<FunctionSymbol> buildAssAndComm = OblCreatorEtrs.buildSymColl(this.assAndComFunctionSymbols);
            result.addAll(OblCreatorEtrs.getCommutativeEquations(buildAssAndComm, FuncSymbolsOfSimpleRules));
            result.addAll(OblCreatorEtrs.getAssociativeEquations(buildAssAndComm, FuncSymbolsOfSimpleRules));
        }
        return result;
    }

    private BasicObligation createVerifiedETRS() {
        final ETRSProblem etrsProblem =
            ETRSProblem.create(
                ImmutableCreator.create(this.simpleRules),
                ImmutableCreator.create(this.computeEquations())
            );
        //At the moment only AC and C Equations are allowed.
        if (etrsProblem.checkACandAandC()) {
            this.language = Language.ETRS;
            return etrsProblem;
        } else {
            final ParseError pe = new ParseError();
            pe.setMessage("Only AC-, A- or C-Equations are supported so far.");
            this.obligationErrors.add(pe);
            this.language = Language.QTRS;
            return null;
        }
    }

    private BasicObligation generateProblem() {
        /* First analyze the given combination.
         * For each existing componenet add the corresponding integer value
         * and save in a String which components have occured for Error handling.
         * Afterwards try to find in the case block a valid combination and build
         * the apropriate proof obligation.
         */
        final boolean relativeNotEmpty = ObligationCreator.notEmpty(this.relativeRules) || ObligationCreator.notEmpty(this.lhsVariableRelRules); 
        final boolean generalizedNotEmpty =
            this.allRules.size() - (this.simpleRules == null ? 0 : this.simpleRules.size()) > 0;
        final boolean conditionalNotEmpty = ObligationCreator.notEmpty(this.conditionalRules);
        final boolean contextSensitiveNotEmptyAndNotNull = this.replacementMap != null && ObligationCreator.notEmpty(this.replacementMap.keySet());

        final boolean equational =
            ObligationCreator.notEmpty(this.equations)
            | ObligationCreator.notEmpty(this.associativeFunctionSymbols)
            | ObligationCreator.notEmpty(this.commutativeFunctionSymbols)
            | ObligationCreator.notEmpty(this.assAndComFunctionSymbols);
        
        final int problemValue = (this.innermost ? ObligationCreator.bitInnermost : 0)
                | (this.outermost ? ObligationCreator.bitOutermost : 0)
                | (this.termination ? ObligationCreator.bitTermination : 0)
        		| (this.ast ? ObligationCreator.bitAST : 0)
                | (this.sast ? ObligationCreator.bitSAST : 0)
                | (generalizedNotEmpty ? ObligationCreator.bitGeneralizedRules : 0)
                | (equational ? ObligationCreator.bitEquational : 0)
                | (relativeNotEmpty ? ObligationCreator.bitRelativeRules : 0)
                | (conditionalNotEmpty ? ObligationCreator.bitConditionalRules : 0)
                | (contextSensitiveNotEmptyAndNotNull ? ObligationCreator.bitContextSensitiveRules : 0)
                | (this.complexity ? ObligationCreator.bitComplexity : 0)
                | (this.basic ? ObligationCreator.bitConstructorbased : 0)
                | (this.innermost ? ObligationCreator.bitInnermost : 0)
                | (this.parallelInnermost ? ObligationCreator.bitParallelInnermost : 0)
                | (this.outermost ? ObligationCreator.bitOutermost : 0)
                | (this.probabilistic ? ObligationCreator.bitProbabilistic : 0)
                | (this.confluence ? ObligationCreator.bitConfluence : 0)
                | (this.infeasibility ? ObligationCreator.bitInfeasibility : 0);

        final String problemCombination =
                        (generalizedNotEmpty ? "Generalized Rules, " : "")
                            + (equational ? "Equational, " : "")
                            + (relativeNotEmpty ? "Relative Rules, " : "")
                            + (conditionalNotEmpty ? "Conditional Rules, " : "")
                            + (contextSensitiveNotEmptyAndNotNull ? "Context Sensitive Rules, " : "")
                            + (this.complexity ? "Complexity Analysis, " : "")
                            + (this.basic ? "Constructor-based (basic), " : "")
                            + (this.innermost ? "Innermost Obligation, " : "")
                            + (this.parallelInnermost ? "Parallel-Innermost Obligation, " : "")
                            + (this.outermost ? "Outermost Obligation, " : "")
                            + (this.innermost ? "Innermost Obligation, " : "")
                            + (this.probabilistic ? "Probabilistic, " : "")
                            + (this.termination ? "Termination, " : "")
                            + (this.ast ? "AST, " : "")
                            + (this.sast ? "SAST, " : "")
                            + (this.confluence ? "Confluence Analysis, " : "")
                            + (this.infeasibility ? "Infeasibility Quenstion, " : "");
        
        final RewriteStrategy strat;
        if(this.innermost) {
            strat = RewriteStrategy.INNERMOST;
        } else if(this.outermost) {
            strat = RewriteStrategy.OUTERMOST;
        } else {
            strat = RewriteStrategy.FULL;
        }

        switch (problemValue) {
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitTermination | ObligationCreator.bitInnermost | ObligationCreator.bitConstructorbased):
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitTermination | ObligationCreator.bitOutermost | ObligationCreator.bitConstructorbased):
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitTermination | ObligationCreator.bitConstructorbased):
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitTermination | ObligationCreator.bitInnermost):
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitTermination | ObligationCreator.bitOutermost):
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitTermination):
                this.language = Language.PTRS;
                return new PTRSProblem(this.probabilisticRules, strat, ProbabilisticTerminationResult.certainTermination, this.basic);
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitAST | ObligationCreator.bitInnermost | ObligationCreator.bitConstructorbased):
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitAST | ObligationCreator.bitOutermost | ObligationCreator.bitConstructorbased):
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitAST | ObligationCreator.bitConstructorbased):
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitAST | ObligationCreator.bitInnermost):
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitAST | ObligationCreator.bitOutermost):
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitAST):
                this.language = Language.PTRS;
                return new PTRSProblem(this.probabilisticRules, strat, ProbabilisticTerminationResult.AST, this.basic);
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitSAST | ObligationCreator.bitInnermost | ObligationCreator.bitConstructorbased):
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitSAST | ObligationCreator.bitOutermost | ObligationCreator.bitConstructorbased):
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitSAST | ObligationCreator.bitConstructorbased):
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitSAST | ObligationCreator.bitInnermost):
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitSAST | ObligationCreator.bitOutermost):
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitSAST):
                this.language = Language.PTRS;
                return new PTRSProblem(this.probabilisticRules, strat, ProbabilisticTerminationResult.SAST, this.basic);
                
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitComplexity | ObligationCreator.bitConstructorbased | ObligationCreator.bitInnermost):
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitComplexity | ObligationCreator.bitConstructorbased | ObligationCreator.bitOutermost):
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitComplexity | ObligationCreator.bitConstructorbased):
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitComplexity | ObligationCreator.bitInnermost):
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitComplexity | ObligationCreator.bitOutermost):
            case (ObligationCreator.bitProbabilistic | ObligationCreator.bitComplexity):
                this.language = Language.CpxPTRS;
                return new PTRS_Cpx_Problem(this.probabilisticRules, strat, ProbabilisticTerminationResult.SAST, this.basic);
                
            case (0): //nothing special, just a plain TRS
                this.language = Language.QTRS;
                return this.getQTRS(null);
    
            case (ObligationCreator.bitInnermost):{
                Set<TRSFunctionApplication> qFunctionApplications = new HashSet<>();
                qFunctionApplications.addAll(CollectionUtils.getLeftHandSides(this.simpleRules));
                this.language = Language.QTRS;
                return this.getQTRS(qFunctionApplications);
            }
    
            case (ObligationCreator.bitRelativeRules): {
                //TODO implement this type!!!
                this.language = Language.RTRS;
                return RelTRSProblem.create((ImmutableCreator.create(this.simpleRules)),
                    (ImmutableCreator.create(this.relativeRules)), (ImmutableCreator.create(this.lhsVariableRelRules)));
            }
            case (
                ObligationCreator.bitRelativeRules
                | ObligationCreator.bitConstructorbased
                | ObligationCreator.bitComplexity
            ):
            case (
                ObligationCreator.bitRelativeRules
                | ObligationCreator.bitConstructorbased
                | ObligationCreator.bitComplexity
                | ObligationCreator.bitInnermost
            ):
            case (
                    ObligationCreator.bitRelativeRules
                    | ObligationCreator.bitConstructorbased
                    | ObligationCreator.bitComplexity
                    | ObligationCreator.bitParallelInnermost
            ): {
                this.language = Language.CpxRelTRS;
                return RuntimeComplexityRelTrsProblem.create(ImmutableCreator.create(this.simpleRules),
                    ImmutableCreator.create(this.relativeRules),
                    this.innermost ? RewriteStrategy.INNERMOST
                        : (this.parallelInnermost ? RewriteStrategy.PARALLEL_INNERMOST : RewriteStrategy.FULL),
                    false);
            }
            case (
                ObligationCreator.bitRelativeRules
                | ObligationCreator.bitComplexity
            ):
            case (
                ObligationCreator.bitRelativeRules
                | ObligationCreator.bitComplexity
                | ObligationCreator.bitInnermost
            ):
            case (
                    ObligationCreator.bitRelativeRules
                    | ObligationCreator.bitComplexity
                    | ObligationCreator.bitParallelInnermost
            ): {
                this.language = Language.CpxRelTRS;
                return DerivationalComplexityRelTrsProblem.create(ImmutableCreator.create(this.simpleRules),
                    ImmutableCreator.create(this.relativeRules),
                    this.innermost ? RewriteStrategy.INNERMOST
                        : (this.parallelInnermost ? RewriteStrategy.PARALLEL_INNERMOST : RewriteStrategy.FULL),
                    false);
                }
            case (ObligationCreator.bitConditionalRules): {
                this.language = Language.CTRS;
                return CTRSProblem.create(ImmutableCreator.create(this.simpleRules),
                    ImmutableCreator.create(this.conditionalRules));
            }
            case (ObligationCreator.bitContextSensitiveRules):
            case (
                ObligationCreator.bitContextSensitiveRules
                | ObligationCreator.bitInnermost
            ): {
                final HashMap<FunctionSymbol, Set<Integer>> newReplacementMap = new HashMap<>();
                //decrease the index of the replacement map as in newTRS Obligation Creator
                for (final Entry<FunctionSymbol, Set<Integer>> entry : replacementMap.entrySet()) {
                    final FunctionSymbol f = entry.getKey();
                    final Set<Integer> oldValues = entry.getValue();
                    final Set<Integer> newValues = new HashSet<>();

                    for(Integer i : oldValues) {
                        newValues.add(i-1);
                    }
                    
                    newReplacementMap.put(f, newValues);
                }
                this.language = Language.CSR;
                final CSRProblem csr = CSRProblem.create(this.simpleRules, newReplacementMap, this.innermost);
                return csr;
            }
    
            case (ObligationCreator.bitEquational):
                return this.createVerifiedETRS();
    
            case (ObligationCreator.bitOutermost):
            case (ObligationCreator.bitGeneralizedRules | ObligationCreator.bitOutermost):
                this.language = Language.OTRS;
                return OTRSProblem.create(this.allRules);
    
            case (ObligationCreator.bitGeneralizedRules):
            case (
                ObligationCreator.bitGeneralizedRules
                | ObligationCreator.bitInnermost
            ):
                this.language = Language.GTRS;
                return GTRSProblem.create(this.allRules, this.innermost);
    
            case (ObligationCreator.bitComplexity
                | ObligationCreator.bitConstructorbased
            ):
            case (ObligationCreator.bitComplexity
                | ObligationCreator.bitConstructorbased
                | ObligationCreator.bitInnermost
            ):
            case (ObligationCreator.bitComplexity
                    | ObligationCreator.bitConstructorbased
                    | ObligationCreator.bitParallelInnermost
            ):
                this.language = Language.CpxTRS;
                return RuntimeComplexityTrsProblem.create(ImmutableCreator.create(this.simpleRules),
                    this.innermost ? RewriteStrategy.INNERMOST
                        : (this.parallelInnermost ? RewriteStrategy.PARALLEL_INNERMOST : RewriteStrategy.FULL));
    
            case (ObligationCreator.bitComplexity
                | ObligationCreator.bitConstructorbased
                | ObligationCreator.bitGeneralizedRules
            ):
            case (ObligationCreator.bitComplexity
                | ObligationCreator.bitConstructorbased
                | ObligationCreator.bitInnermost
                | ObligationCreator.bitGeneralizedRules
            ):
                this.language = Language.CpxTRS;
                return new CpxGTrsProblem(this.allRules);
    
            case (ObligationCreator.bitComplexity):
            case (
                ObligationCreator.bitComplexity
                | ObligationCreator.bitInnermost
            ):
            case (
                    ObligationCreator.bitComplexity
                    | ObligationCreator.bitParallelInnermost
            ):
                this.language = Language.CpxTRS;
                return DerivationalComplexityTrsProblem.create(ImmutableCreator.create(this.simpleRules),
                    this.innermost ? RewriteStrategy.INNERMOST
                        : (this.parallelInnermost ? RewriteStrategy.PARALLEL_INNERMOST : RewriteStrategy.FULL));
    
            case(ObligationCreator.bitConfluence):
                this.language = Language.ConfTRS;
                return ConfTRSProblem.create(ImmutableCreator.create(this.simpleRules));
                
            default: {
                final ParseError pe = new ParseError();
                if(problemCombination.length() == 0) {
                    pe.setMessage(
                            "Missing information! (E.g. no Goal is defined)"
                        );
                } else {
                    pe.setMessage(
                            "The combination of "
                            + problemCombination.substring(0, (problemCombination.length() - 2))
                            + " is not allowed!"
                        );
                }
                this.obligationErrors.add(pe);
                return null;
            }
        }
    }
    
    private void getAll(final RawAriTrs rawtrs) {
        this.simpleRules = rawtrs.getSimpleRules();
        this.allRules = rawtrs.getAllRules();
        this.equations = rawtrs.getEquations();
        this.relativeRules = rawtrs.getRelativeRules();
        this.conditionalRules = rawtrs.getConditionalRules();
        this.replacementMap = rawtrs.getContextSensitiveRules();
        this.complexity = rawtrs.isComplexity();
        this.innermost = rawtrs.getInnermost();
        this.parallelInnermost = rawtrs.getParellelInnermost();
        this.outermost = rawtrs.getOutermost();
        this.setAssociativeFunctionSymbols(rawtrs.getAssociativeFunctionSymbols());
        this.setCommutativeFunctionSymbols(rawtrs.getCommutativeFunctionSymbols());
        this.setAssAndComFunctionSymbols(rawtrs.getAssAndCommFunctionSymbols());
        this.lhsVariableRelRules = rawtrs.getAllLHSVariableRules();
        this.innermost = rawtrs.isInnermost();
        this.outermost = rawtrs.isOutermost();
        this.termination = rawtrs.isTermination();
        this.ast = rawtrs.isAst();
        this.sast = rawtrs.isSast();
        this.probabilisticRules = rawtrs.getProbabilisticRules();
        this.basic = rawtrs.isBasic();
        this.probabilistic = rawtrs.getInputFormat() == InputFormat.PTRS;
        this.confluence = rawtrs.isConfluence();
        this.infeasibility = rawtrs.isInfeasibility();
        this.infeasibilityQuery = rawtrs.getInfeasibilityQuery();
    }

    private QTRSProblem getQTRS(Set<TRSFunctionApplication> qFunctionApplications) {
        if (qFunctionApplications == null) {
            return QTRSProblem.create(ImmutableCreator.create(this.simpleRules));
        }
        return QTRSProblem.create(ImmutableCreator.create(this.simpleRules), qFunctionApplications);
    }

    private void setAssAndComFunctionSymbols(Set<FunctionSymbol> assAndCommFunctionSymbols) {
        if (ObligationCreator.notEmpty(assAndCommFunctionSymbols)) {
            this.assAndComFunctionSymbols = new TreeSet<FunctionSymbol>();
            this.assAndComFunctionSymbols.addAll(assAndCommFunctionSymbols);
        } else {
            this.assAndComFunctionSymbols = null;
        }
    }

    private void setAssociativeFunctionSymbols(final Set<FunctionSymbol> associativeFunctionSymbols) {
        if (ObligationCreator.notEmpty(associativeFunctionSymbols)) {
            this.associativeFunctionSymbols = new TreeSet<FunctionSymbol>();
            this.associativeFunctionSymbols.addAll(associativeFunctionSymbols);
        } else {
            this.associativeFunctionSymbols = null;
        }
    }

    private void setCommutativeFunctionSymbols(final Set<FunctionSymbol> commutativeFunctionSymbols) {
        if (ObligationCreator.notEmpty(commutativeFunctionSymbols)) {
            this.commutativeFunctionSymbols = new TreeSet<FunctionSymbol>();
            this.commutativeFunctionSymbols.addAll(commutativeFunctionSymbols);
        } else {
            this.commutativeFunctionSymbols = null;
        }
    }
}
