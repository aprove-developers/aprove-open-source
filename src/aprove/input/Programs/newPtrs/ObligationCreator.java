package aprove.input.Programs.newPtrs;

import java.util.*;

import aprove.input.Utility.*;
import aprove.prooftree.Obligations.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Input.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Complexity.PTRSProblem.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;

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
    private final static int bitInnermost = 1 << 1;
    private final static int bitOutermost = 1 << 2;
    private final static int bitTermination = 1 << 3;
    private final static int bitAST = 1 << 4;
    private final static int bitSAST = 1 << 5;
    private final static int bitComplexity = 1 << 6;

    /*
     * Declaration of the Constructs to which the parser will
     * collect information.
     */
    private boolean innermost;
    private boolean outermost;
    private boolean termination;
    private boolean ast;
    private boolean sast;
    private boolean basic;
    private boolean complexity;
    private Language language = null;
    private final List<ParseError> obligationErrors;
    private Set<ProbabilisticRule> probabilisticRules;

    public ObligationCreator(final RawPtrs fullpass) {
        this.obligationErrors = new LinkedList<ParseError>();
        this.getAll(fullpass);
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

    private BasicObligation generateProblem() {
        /* First analyze the given combination.
         * For each existing componenet add the corresponding integer value
         * and save in a String which components have occured for Error handling.
         * Afterwards try to find in the case block a valid combination and build
         * the apropriate proof obligation.
         */
        final int problemValue = (this.innermost ? ObligationCreator.bitInnermost : 0)
                | (this.outermost ? ObligationCreator.bitOutermost : 0)
                | (this.termination ? ObligationCreator.bitTermination : 0)
        		| (this.ast ? ObligationCreator.bitAST : 0)
                | (this.sast ? ObligationCreator.bitSAST : 0)
                | (this.complexity ? ObligationCreator.bitComplexity : 0);

        final String problemCombination = 
                (this.innermost ? "Innermost Obligation, " : "")
                + (this.termination ? "Termination, " : "")
                + (this.complexity ? "Complexity Analysis, " : "")
		        + (this.ast ? "AST, " : "")
		        + (this.sast ? "SAST, " : "");
        
        final RewriteStrategy strat;
        if(this.innermost) {
            strat = RewriteStrategy.INNERMOST;
        } else if(this.outermost) {
            strat = RewriteStrategy.OUTERMOST;
        } else {
            strat = RewriteStrategy.FULL;
        }

        switch (problemValue) {
        case (ObligationCreator.bitTermination | ObligationCreator.bitInnermost):
        case (ObligationCreator.bitTermination | ObligationCreator.bitOutermost):
        case (ObligationCreator.bitTermination):
            this.language = Language.PTRS;
            return new PTRSProblem(this.probabilisticRules, strat, ProbabilisticTerminationResult.certainTermination, this.basic);
        case (ObligationCreator.bitAST | ObligationCreator.bitInnermost):
        case (ObligationCreator.bitAST | ObligationCreator.bitOutermost):
        case (ObligationCreator.bitAST):
            this.language = Language.PTRS;
            return new PTRSProblem(this.probabilisticRules, strat, ProbabilisticTerminationResult.AST, this.basic);
        case (ObligationCreator.bitSAST | ObligationCreator.bitInnermost):
        case (ObligationCreator.bitSAST | ObligationCreator.bitOutermost):
        case (ObligationCreator.bitSAST):
            this.language = Language.PTRS;
            return new PTRSProblem(this.probabilisticRules, strat, ProbabilisticTerminationResult.SAST, this.basic);
            
        case (ObligationCreator.bitComplexity | ObligationCreator.bitInnermost):
        case (ObligationCreator.bitComplexity | ObligationCreator.bitOutermost):
        case (ObligationCreator.bitComplexity):
            this.language = Language.CpxPTRS;
            return new PTRS_Cpx_Problem(this.probabilisticRules, strat, ProbabilisticTerminationResult.SAST, this.basic);

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

    private void getAll(final RawPtrs rawptrs) {
        this.innermost = rawptrs.isInnermost();
        this.outermost = rawptrs.isOutermost();
        this.termination = rawptrs.isTermination();
        this.complexity = rawptrs.isComplexity();
        this.ast = rawptrs.isAst();
        this.sast = rawptrs.isSast();
        this.probabilisticRules = rawptrs.getProbabilisticRules();
        this.basic = rawptrs.isBasic();
    }
}
