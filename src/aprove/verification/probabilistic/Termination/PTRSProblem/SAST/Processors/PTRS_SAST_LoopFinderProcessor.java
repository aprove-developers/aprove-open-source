package aprove.verification.probabilistic.Termination.PTRSProblem.SAST.Processors;

import java.util.*;
import java.util.Map.*;
import java.util.logging.*;

import org.apache.commons.math3.fraction.*;

import aprove.prooftree.Export.Utility.*;
import aprove.prooftree.Proofs.*;
import aprove.strategies.Abortions.*;
import aprove.strategies.Annotations.*;
import aprove.verification.dpframework.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.dpframework.DPProblem.*;
import aprove.verification.dpframework.DPProblem.Processors.*;
import aprove.verification.dpframework.TRSProblem.*;
import aprove.verification.oldframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;
import aprove.verification.probabilistic.BasicStructures.*;
import aprove.verification.probabilistic.Termination.PTRSProblem.*;
import immutables.*;

/**
 * Processor that searches for looping terms
 * and then tries to disprove SAST by embedding a random walk.
 *
 * @author J-C Kassing & Henri Nagel & Alexander Schlecht
 * @version $Id$
 */
public class PTRS_SAST_LoopFinderProcessor extends PTRS_SAST_ProblemProcessor {

    private Arguments args;
    private boolean allcuts;

    /**
     * logger to be used
     */
    private final Logger log = Logger.getLogger("aprove.verification.dpframework.DPProblem.Processors.QDPNonLoopProcessor");

    @ParamsViaArgumentObject
    public PTRS_SAST_LoopFinderProcessor(final Arguments args) {
        this.args = args;
        this.allcuts = args.allcuts;
    }

    // ================================================================================
    // isApplicable
    // ================================================================================

    @Override
    public boolean isPTRSApplicable(final PTRSProblem ptrs) {
        return true;
    }

    // ================================================================================
    // Processing
    // ================================================================================

    @Override
    public Result processPTRSProblem(final PTRSProblem ptrs, final Abortion aborter) throws AbortionException {

        //Create SymbolTransitionGraph
        final SymbolTransitionGraph stg = new SymbolTransitionGraph(ptrs);

        //List for all already found trees
        final List<NonTerminationProbProofNode> trees = new ArrayList<>();

        //Transform problem to QDPProblem
        final QTRSProblem qtrs = ptrs.getNonProbAbstraction();
        final ImmutableTriple<ImmutableSet<Rule>, ImmutableMap<FunctionSymbol, FunctionSymbol>, ImmutableMap<Rule, List<Pair<Position, Rule>>>> dps =
            qtrs.getDPs();
        final QDPProblem qdpProblem = QDPProblem.create(dps.x, qtrs, true);
        final NonTerminationProcedure proc =
            new NonTerminationProcedure(NonTerminationProcessor.procNumber.getAndIncrement(), qdpProblem, 4, 0, 4, NonTerminationProcessor.Heuristic.NORMAL);
        Result qdpResult = null;

        while (true) {
            aborter.checkAbortion();
            TRSTerm loopTerm = null;
            ImmutableList<Pair<Position, Rule>> rewriteSeq = null;
            Proof proof = null;

            //Suche nach neuer Loop mit dem QDP Problem
            if (proc.reachedClosure()) {
                qdpResult = proc.doClosureAgain(aborter);
            } else {
                qdpResult = proc.processQDPProblem(aborter);
            }

            if (qdpResult != null && qdpResult.getObligationChild() != null) {
                proof = qdpResult.getObligationChild().getProof();
            }

            //Überprüfen ob es eine Loop gab
            if (proof != null && proof instanceof final NonTerminationLoopProof ntProof) {

                //Extrahieren des Loopsymbols
                final TRSTerm loopTermBig = ntProof.getNarrowPair().x;
                rewriteSeq = ntProof.getNarrowPair().getRewriteSeq();

                //Suche nach dem loopendem Term
                //dps.z.entrySet() enthält die originalen Regeln und auf welche großen Terme diese gemappt wurden
                for (final Map.Entry<Rule, List<Pair<Position, Rule>>> entry : dps.z.entrySet()) {
                    final List<Pair<Position, Rule>> ruleBig = entry.getValue();
                    final TRSSubstitution matcher = ruleBig.get(0).getValue().getLeft().getMatcher(loopTermBig);
                    if (matcher != null) {
                        //Den Loopenden Term in groß gefunden & den normalen loopTerm mit dem Matcher erstellen
                        loopTerm = entry.getKey().getLeft().applySubstitution(matcher);
                    }
                }

                // The terms in our trees are always in standard representation
                loopTerm = loopTerm.getStandardRenumbered();

                NonTerminationProbProofNode tree = null;
                //Gucken ob loopTerm schon ausgewertet wurde
                for (final NonTerminationProbProofNode oldTree : trees) {

                    if (oldTree.getValue().getX().getStandardRenumbered().equals(loopTerm.getStandardRenumbered())) {
                        //Baum existiert schon
                        tree = oldTree;
                        break;
                    }
                }

                //TODO: Strip the loopterm to only consist of necessary parts for the loop

                if (tree == null) {
                    //If there is no tree, then create one for the loop
                    final List<Triple<TRSTerm, TRSSubstitution, Pair<BigFraction, BigFraction>>> subtermsWithZero = new ArrayList<>();
                    final Set<Position> positions = loopTerm.getPositions();

                    if (this.allcuts) {
                        //All cuts (linear and orthogonal)
                        final BiTreeNode<Pair<Position, TRSTerm>> termTree = loopTerm.getTreeRep();
                        final var cutsSet = orthogonalCutNodes(termTree, true);
                        NextCut: for (final Set<BiTreeNode<Pair<Position, TRSTerm>>> cutNodes : cutsSet) { //Iterate over all possible cuts 

                            //Filter variable subterms
                            final Map<Position, TRSTerm> cutMap = new HashMap<>();
                            for (final var n : cutNodes) {
                                final Position pos = n.getValue().x;
                                final TRSTerm sub = n.getValue().y;
                                if (!sub.isVariable()) {
                                    cutMap.put(pos, sub);
                                }
                            }
                            if (cutMap.isEmpty()) {
                                continue NextCut;
                            }

                            //Take all variables that exist in the cuts
                            final Set<TRSVariable> used = new HashSet<>();
                            for (final TRSTerm termInCut : cutMap.values()) {
                                //To generalize: we require cutting parts that contain at least one variable
                                if (termInCut.getVariables().size() == 0) {
                                    continue NextCut;
                                }
                                used.addAll(termInCut.getVariables());
                            }

                            //build substitution sigma = { v -> originalSubtermAtPos }
                            //for all possible infinite substitutions

                            final List<Map<TRSVariable, Entry<Position, TRSTerm>>> listOfMaps =
                                generateAllMappings(new ArrayList<>(used), new ArrayList<>(cutMap.entrySet()));

                            NextMap: for (final Map<TRSVariable, Entry<Position, TRSTerm>> complex_map : listOfMaps) {

                                final Map<TRSVariable, TRSTerm> substitutionMap = new LinkedHashMap<>();
                                for (final Entry<TRSVariable, Entry<Position, TRSTerm>> e : complex_map.entrySet()) {
                                    substitutionMap.put(e.getKey(), e.getValue().getValue());
                                }
                                final TRSSubstitution sigma = TRSSubstitution.create(ImmutableCreator.create(substitutionMap));

                                // Replace all positions in the term
                                TRSTerm t2 = loopTerm;

                                for (final Entry<TRSVariable, Entry<Position, TRSTerm>> e : complex_map.entrySet()) {
                                    t2 = t2.replaceAt(e.getValue().getKey(), e.getKey());
                                }

                                // check whether the base term + pumping results in the looping term
                                if (!t2.applySubstitution(sigma).equals(loopTerm)) {
                                    continue NextMap;
                                }

                                // check whether the pumping substitution generalizes
                                for (final TRSVariable var : sigma.getDomain()) {
                                    boolean containsVar = false;
                                    for (final TRSTerm termInCodomain : sigma.getCodomain()) {
                                        if (termInCodomain.getVariables().contains(var)) {
                                            containsVar = true;
                                        }
                                    }
                                    if (!containsVar) {
                                        continue NextMap;
                                    }
                                }

                                final Triple<TRSTerm, TRSSubstitution, Pair<BigFraction, BigFraction>> newTriple =
                                    new Triple<>(t2,
                                        sigma,
                                        new Pair<>(BigFraction.ZERO, BigFraction.ZERO));

                                if (!subtermsWithZero.contains(newTriple)) {
                                    subtermsWithZero.add(newTriple);
                                }
                            }
                        }
                    } else {
                        //Linear cuts only
                        //Create all possible linear term + substitution splits for counting
                        for (final Position p : positions) {
                            final Set<Position> createVariableAtPositions = findChildPositions(p, positions);

                            if (createVariableAtPositions.isEmpty()) {
                                continue;
                            }

                            for (final Position variablePosition : createVariableAtPositions) {
                                //If subterm is a variable, do nothing
                                if (loopTerm.getSubterm(variablePosition).isVariable()) {
                                    continue;
                                }

                                //If subterm contains more than one variable, do nothing
                                final int numberVars = loopTerm.getSubterm(variablePosition).getVariables().size();
                                if (numberVars == 0 || numberVars >= 2) {
                                    continue;
                                }

                                //If the variable occurs more than once in the term, do nothing
                                final TRSVariable var = loopTerm.getSubterm(variablePosition).getVariables().iterator().next();
                                if (loopTerm.getVariablePositions().get(var).size() >= 2) {
                                    continue;
                                }

                                //Split term and create substitution
                                final TRSSubstitution substitution = TRSSubstitution.create(var, loopTerm.getSubterm(variablePosition));
                                final Triple<TRSTerm, TRSSubstitution, Pair<BigFraction, BigFraction>> newTriple =
                                    new Triple<>(loopTerm.replaceAt(variablePosition, var),
                                        substitution,
                                        new Pair<>(BigFraction.ZERO, BigFraction.ZERO));
                                if (!subtermsWithZero.contains(newTriple)) {
                                    subtermsWithZero.add(newTriple);
                                }
                            }
                        }
                    }

                    //Finally, add the full term without any substitution
                    subtermsWithZero.add(
                        new Triple<>(loopTerm, null, new Pair<>(BigFraction.ZERO, BigFraction.ZERO)));
                    tree = new NonTerminationProbProofNode(new ProofNodeContent(loopTerm, BigFraction.ONE, subtermsWithZero));
                    trees.add(tree);
                }

                //---------------------------------------------//
                // Create the tree including at least the loop //
                //---------------------------------------------//
                List<Pair<NonTerminationProbProofNode, Position>> currentLeaves = new ArrayList<>();
                currentLeaves.add(new Pair<>(tree, Position.EPSILON));
                for (int i = 0; i < rewriteSeq.size(); i++) {
                    aborter.checkAbortion();

                    final List<Pair<NonTerminationProbProofNode, Position>> newLeaves = new ArrayList<>();
                    //Berechne die Rewritings
                    for (final Pair<NonTerminationProbProofNode, Position> leaf : currentLeaves) {
                        final List<Pair<NonTerminationProbProofNode, Position>> newChildsForSingleLeaf =
                            computeChildrenForStepIfPossible(ptrs.getPR(), loopTerm, leaf, rewriteSeq.get(i), dps, ptrs);
                        newLeaves.addAll(newChildsForSingleLeaf);
                    }
                    currentLeaves = newLeaves;
                }

                //-----------------------------------------------------------------------------//
                // Cut the tree such that it only contains the loop and no other useless edges //
                //-----------------------------------------------------------------------------//
                aborter.checkAbortion();
                //Get all created trees
                List<NonTerminationProbProofNode> curLeaves = new ArrayList<>();
                tree.collectLeavesAtLevel(0, tree.getDepth(), curLeaves);
                NonTerminationProbProofNode loopingLeaf = null;

                //Pick a Leaf that contains our starting loopterm
                for (final NonTerminationProbProofNode leaf : curLeaves) {
                    loopingLeaf = leaf; //TODO
                    break;
                }

                //Cut tree to only contain the path to this leaf
                tree.onlyPathTo(loopingLeaf);

                //----------------------------------------------------------//
                // Check if the tree is a single path (we have a loop walk) //
                //----------------------------------------------------------//
                curLeaves = new ArrayList<>();
                tree.collectLeaves(curLeaves);

                for (final NonTerminationProbProofNode leaf : curLeaves) {
                    //If there is a leaf with probability 1, then we have a loop walk.
                    if (leaf.getValue().y.equals(BigFraction.ONE)) {
                        return ResultFactory.disproved(new SASTLoopFinderProof(tree, rewriteSeq, tree.isMaxValueAllCounts()));
                    }
                }

                //--------------------------------------------------------------------------------//
                // Rewrite the leaves of the tree until we hit the threshold or find enough loops //
                //--------------------------------------------------------------------------------//
                final int rewriteStepIterations = this.args.MAXITERATIONSTREE < 0 ? Integer.MAX_VALUE : this.args.MAXITERATIONSTREE;
                while (tree.getDepth() <= rewriteStepIterations) {
                    aborter.checkAbortion();

                    //If we can disprove PAST (hence SAST), stop
                    if (tree.getMaxValue().compareTo(BigFraction.ONE) >= 0) {
                        return ResultFactory.disproved(new SASTLoopFinderProof(tree, rewriteSeq, tree.isMaxValueAllCounts()));
                    }

                    //Get all trees we can extend
                    curLeaves = new ArrayList<>();
                    tree.collectLeaves(curLeaves);

                    //Compute the possible rewrite steps
                    boolean rewriteStepHappened = false;
                    for (final NonTerminationProbProofNode leaf : curLeaves) { //First, we do not rewrite terms with an occurrence of the looping term
                        rewriteStepHappened |= computeChildren(ptrs, leaf, loopTerm, stg, false);
                    }

                    if (!rewriteStepHappened) { //If nothing changed, then we also allow rewrite steps at terms with an occurrence of the looping term
                        for (final NonTerminationProbProofNode leaf : curLeaves) {
                            computeChildren(ptrs, leaf, loopTerm, stg, true);
                        }
                    }
                }
            } else {
                //There is no term or no loop at all anymore
                if (trees.isEmpty()) {
                    return ResultFactory.unsuccessful();
                }
                //There is no further term, just rewrite as long as possible
                while (true) {
                    for (final NonTerminationProbProofNode tree : trees) {
                        aborter.checkAbortion();
                        //Get all trees we can extend
                        final List<NonTerminationProbProofNode> currentLeaves = new ArrayList<>();
                        tree.collectLeavesAtLevel(0, tree.getDepth(), currentLeaves);

                        //Compute the possible rewrite steps
                        for (final NonTerminationProbProofNode leaf : currentLeaves) {
                            computeChildren(ptrs, leaf, tree.getValue().getX(), stg, true);
                        }
                        //If we can disprove PAST (hence SAST), stop
                        if (tree.getMaxValue().compareTo(BigFraction.ONE) >= 0) {
                            return ResultFactory.disproved(new SASTLoopFinderProof(tree, rewriteSeq, tree.isMaxValueAllCounts()));
                        }
                    }
                }
            }
        }
    }

    /**
     * Helper Function:
     * Generate a list of all possible bijective mappings between both lists.
     */
    private <A, B> ImmutableList<Map<A, B>> generateAllMappings(final List<A> A, final List<B> B) {
        if (A.isEmpty()) {
            final List<Map<A, B>> res = new ArrayList<>();
            res.add(new LinkedHashMap<>());
            return ImmutableCreator.create(res);
        }

        final A firstA = A.get(0);
        final List<A> restA = A.subList(1, A.size());

        final List<Map<A, B>> result = new ArrayList<>();

        for (final B chosenB : B) {
            for (final Map<A, B> partial : generateAllMappings(restA, B)) {
                final Map<A, B> mapping = new LinkedHashMap<>();
                mapping.put(firstA, chosenB);
                mapping.putAll(partial);
                result.add(mapping);
            }
        }

        return ImmutableCreator.create(result);
    }

    /**
     * Returns all positions in the set that are direct children of the given parent position.
     * A position is considered a child if it starts with the parent and is exactly one level deeper.
     * Example: [1,1] and [1,0] are children of [1].
     *
     * @param parent the parent position
     * @param positions the set of positions to search
     * @return the subset of positions that are direct children of the parent
     */

    private Set<Position> findChildPositions(final Position parent, final Set<Position> positions) {
        final Set<Position> res = new HashSet<>();
        for (final Position p : positions) {
            if (parent.isPrefixOf(p) && p.toIntArray().length == parent.toIntArray().length + 1) {
                res.add(p);
            }
        }
        return res;
    }

    /**
     * Computes and adds the children of the given leaf node based on the provided set of probabilistic rules.
     *
     * @param rules the set of probabilistic rules used for computation
     * @param leaf the leaf node for which children are computed
     */
    private boolean
        computeChildren(final PTRSProblem pqtrs,
            final NonTerminationProbProofNode leaf,
            final TRSTerm loopTerm,
            final SymbolTransitionGraph stg,
            final boolean rewriteIfLoopOccurs) {
        //Get the term and positions
        final Set<ProbabilisticRule> rules = pqtrs.getPR();
        final TRSTerm term = leaf.getValue().getX();
        final BigFraction weight = leaf.getValue().getY();
        final Set<Position> positions = new HashSet<>();
        positions.addAll(term.getPositions());

        //Check if we already know that the term should not be further evaluated
        if (!leaf.isPossibleToReachLoop()) {
            return false;
        }

        //Check if some subterm of term can potentially reach loopTerm
        boolean isReachable = false;
        for (final TRSTerm subterm : term.getSubTerms()) {
            if (subterm instanceof final TRSFunctionApplication fapp) {
                isReachable |= stg.isReachable(fapp.getFunctionSymbol(), ((TRSFunctionApplication) loopTerm).getFunctionSymbol());
            }
        }
        if (!isReachable) {
            leaf.setPossibleToReachLoop(false);
            return false;
        }

        //Check if the term has an occurrence of the loop
        final int countcurrentOrtho = countMatches(leaf.getValue().getX(), loopTerm, null, true);
        if (countcurrentOrtho >= 1 && !rewriteIfLoopOccurs) {// Do not rewrite if the loop already occurs
            return false;
        }

        boolean performedRewriteStep = false;
        //Look at which position we can apply a rule
        for (final ProbabilisticRule r : rules) {

            //The terms within our trees are always in standard representation
            //And the rule to be in second prefix standard representation
            final ProbabilisticRule ruleSecondPrefix = r.getWithRenumberedVariables(TRSTerm.SECOND_STANDARD_PREFIX);

            for (final Position pi : positions) {
                final TRSTerm t = term.getSubterm(pi);
                if (!t.isVariable()) {
                    final TRSSubstitution matcher = ruleSecondPrefix.getLeft().getMatcher(t);
                    if (matcher != null) {
                        //We can apply the rule r at position p from term
                        final List<NonTerminationProbProofNode> res = new ArrayList<>();
                        //calculate the multiDistribution for the applied rule r
                        final Map<TRSTerm, BigFraction> multDist = term.rewriteWithProbOfTerm(ruleSecondPrefix, pi, matcher, weight).getSupportMapping();
                        for (final Entry<TRSTerm, BigFraction> entry : multDist.entrySet()) {
                            final TRSTerm child = entry.getKey();
                            final BigFraction fraction = entry.getValue();
                            final List<Triple<TRSTerm, TRSSubstitution, Pair<BigFraction, BigFraction>>> valuesList = new ArrayList<>();
                            //calculate all potentials for the child term
                            for (int i = 0; i < leaf.getValue().getZ().size(); i++) {

                                BigFraction countAll = BigFraction.MINUS_ONE;
                                //Check if we are allowed to use all occurrences
                                if (loopTerm.isLinear() || child.containsVariablesAsOften(loopTerm.getVariablePositions())) {
                                    countAll = fraction.multiply(
                                        countMatches(child, leaf.getValue().getZ().get(i).getX(), leaf.getValue().getZ().get(i).getY(), false));
                                }
                                //Counting orthogonal occurrences is always allowed
                                final BigFraction countOrtho = fraction.multiply(
                                    countMatches(child, leaf.getValue().getZ().get(i).getX(), leaf.getValue().getZ().get(i).getY(), true));

                                //Update
                                valuesList.add(new Triple<>(
                                    leaf.getValue().getZ().get(i).getX(),
                                    leaf.getValue().getZ().get(i).getY(),
                                    new Pair<>(countAll, countOrtho)));
                            }
                            res.add(new NonTerminationProbProofNode(new ProofNodeContent(child, fraction, valuesList)));
                        }
                        //Add the new child to the leaf
                        leaf.addNewRewriteOption(res);
                        performedRewriteStep = true;
                    }
                }
            }

        }
        return performedRewriteStep;
    }

    /**
     * Computes and adds the children of the given leaf node based on the provided set of probabilistic rules.
     *
     * @param rules the set of probabilistic rules used for computation
     * @param leaf the leaf node for which children are computed
     * @param dps
     */
    private List<Pair<NonTerminationProbProofNode, Position>> computeChildrenForStepIfPossible(final Set<ProbabilisticRule> rules,
        final TRSTerm loopTerm,
        final Pair<NonTerminationProbProofNode, Position> leaf,
        final Pair<Position, Rule> step,
        final ImmutableTriple<ImmutableSet<Rule>, ImmutableMap<FunctionSymbol, FunctionSymbol>, ImmutableMap<Rule, List<Pair<Position, Rule>>>> dps,
        final PTRSProblem qtrs) {

        //Get the term and positions
        final TRSTerm term = leaf.x.getValue().getX();
        final BigFraction weight = leaf.x.getValue().getY();
        final Set<Position> positions = new HashSet<>();
        positions.addAll(term.getPositions());

        final Position chi = leaf.y; //Position of the Context hole due to DP steps
        final Position pi = step.x; //Position where we applied the rule
        final Position chipi = chi.append(pi); //Position where we applied the rule
        Position tau = Position.EPSILON; //Position of DP

        //Get ordinary rewrite rule for the step if it is a P step
        Rule origRule = step.y;
        final FunctionSymbol f = origRule.getLeft().getRootSymbol();
        if (dps.y.containsValue(f)) {
            SearchForRule: for (final Entry<Rule, List<Pair<Position, Rule>>> dpMap : dps.z.entrySet()) {
                for (final Pair<Position, Rule> DP : dpMap.getValue()) {
                    if (DP.y.getStandardRepresentation().equals(origRule.getStandardRepresentation())) {
                        origRule = dpMap.getKey();
                        tau = DP.getKey();
                        break SearchForRule;
                    }
                }
            }
        }
        final Position chitau = chi.append(tau); //Position where we applied the rule

        //Get original probabilistic rewrite rule for the step
        ProbabilisticRule origProbRule = null;
        SearchForProbRule: for (final ProbabilisticRule prule : qtrs.getPR()) {
            for (final Rule pruleAbs : prule.getNonProbabilisticRepresentation()) {
                if (pruleAbs.getStandardRepresentation().equals(origRule.getStandardRepresentation())) {
                    origProbRule = prule;
                    break SearchForProbRule;
                }
            }
        }

        //The terms within our trees are always in standard representation
        //And the rule to be in second prefix standard representation
        origProbRule = origProbRule.getWithRenumberedVariables(TRSTerm.SECOND_STANDARD_PREFIX);

        //Check if we can apply the rule:
        if (term.getPositions().contains(chipi) && origProbRule.getLeft().matches(term.getSubterm(chipi))) {
            final List<Pair<NonTerminationProbProofNode, Position>> res = new ArrayList<>();
            final List<NonTerminationProbProofNode> children = new ArrayList<>();
            final TRSSubstitution matcher = origProbRule.getLeft().getMatcher(term.getSubterm(chipi));
            if (matcher != null) {
                //We can apply the rule r at position p from term
                //calculate the multiDistribution for the applied rule r
                final Map<TRSTerm, BigFraction> multDist = term.rewriteWithProbOfTerm(origProbRule, chipi, matcher, weight).getSupportMapping();
                for (final Entry<TRSTerm, BigFraction> entry : multDist.entrySet()) {
                    final TRSTerm child = entry.getKey();
                    final BigFraction fraction = entry.getValue();
                    final List<Triple<TRSTerm, TRSSubstitution, Pair<BigFraction, BigFraction>>> valuesList = new ArrayList<>();
                    //calculate all potentials for the child term
                    for (int i = 0; i < leaf.x.getValue().getZ().size(); i++) {
                        BigFraction countAll = BigFraction.MINUS_ONE;
                        //Check if we are allowed to use all occurrences
                        if (loopTerm.isLinear() || child.containsVariablesAsOften(loopTerm.getVariablePositions())) {
                            countAll = fraction.multiply(
                                countMatches(child, leaf.x.getValue().getZ().get(i).getX(), leaf.x.getValue().getZ().get(i).getY(), false));
                        }
                        //Counting orthogonal occurrences is always allowed
                        final BigFraction countOrtho = fraction.multiply(
                            countMatches(child, leaf.x.getValue().getZ().get(i).getX(), leaf.x.getValue().getZ().get(i).getY(), true));

                        valuesList.add(new Triple<>(
                            leaf.x.getValue().getZ().get(i).getX(),
                            leaf.x.getValue().getZ().get(i).getY(),
                            new Pair<>(countAll, countOrtho)));
                    }
                    final NonTerminationProbProofNode newChild = new NonTerminationProbProofNode(new ProofNodeContent(child, fraction, valuesList));
                    children.add(newChild);
                    res.add(new Pair<>(newChild, chitau));
                }
                //Add the new child to the leaf
                leaf.x.addNewRewriteOption(children);
            }
            return res;
        } else {
            // Do nothing, this was the wrong path for the loop.
            return new ArrayList<>();
        }
    }

    /**
     * Counts how often the baseLoopTerm, with the given repeatingSubstitution applied repeatedly, matches the targetTerm.
     * Returns -1 if baseLoopTerm does not match targetTerm even once and a substitution is provided.
     *
     * @param targetTerm the term to match against
     * @param baseLoopTerm the term representing the loop's base form
     * @param repeatingSubstitution the substitution repeatedly applied to baseLoopTerm
     * @return the number of successful matches, or -1 if no match occurs and a substitution is provided
     */
    private int countMatches(final TRSTerm targetTerm, final TRSTerm baseLoopTerm, final TRSSubstitution repeatingSubstitution, final boolean onlyOrtho) {
        if (baseLoopTerm == null) {
            return 0;
        } else if (repeatingSubstitution == null) {
            if (!onlyOrtho) { // Count All Occurrences
                return targetTerm.maxNO(baseLoopTerm);
            } else { // Count Orthogonal
                return targetTerm.maxOO(baseLoopTerm);
            }
        } else {
            // Currently, we can only handle orthogonal counting in the case of pattern terms
            //          if (!onlyOrtho) { // Count All Occurrences
            //              int maxNM = targetTerm.maxNM(baseLoopTerm, repeatingSubstitution);
            //              if (maxNM == 0) { // Check if the baseLoopTerm exists as subterm at all
            //                  return targetTerm.hasPatternOcc(baseLoopTerm, repeatingSubstitution) ? 0 : -1;
            //              } else {
            //                  return maxNM;
            //              }
            //          } else { // Count Orthogonal
            final int maxOM = targetTerm.maxOM(baseLoopTerm, repeatingSubstitution);
            if (maxOM == 0) { // Check if the baseLoopTerm exists as subterm at all
                return targetTerm.hasPatternOcc(baseLoopTerm, repeatingSubstitution) ? 0 : -1;
            } else {
                return maxOM;
            }
            //            }
        }
    }

    /**
     * Enumerate all orthogonal node sets by recursion on the argument term tree
     *
     * @param node tree/ subtree from where we search for cuts
     * @param allowCutHere boolean if we allow cut at root of node
     * @return List of all orthogonal node sets
     */
    private static List<Set<BiTreeNode<Pair<Position, TRSTerm>>>> orthogonalCutNodes(
        final BiTreeNode<Pair<Position, TRSTerm>> node,
        final boolean allowCutHere) {
        final List<Set<BiTreeNode<Pair<Position, TRSTerm>>>> res = new ArrayList<>();

        // Option A: cut here
        if (allowCutHere) {
            final Set<BiTreeNode<Pair<Position, TRSTerm>>> s = new HashSet<>();
            s.add(node);
            res.add(s);
        }

        // Option B: don't cut here -> union of choices from children
        final List<BiTreeNode<Pair<Position, TRSTerm>>> kids = node.getChildren();
        if (kids.isEmpty()) {
            // leaf: if we didn't cut here, that's "choose nothing"
            res.add(Collections.emptySet());
            return res;
        }

        // Cartesian product of child choices
        List<Set<BiTreeNode<Pair<Position, TRSTerm>>>> acc = new ArrayList<>();
        acc.add(new HashSet<>());

        for (final var child : kids) {
            final List<Set<BiTreeNode<Pair<Position, TRSTerm>>>> childChoices =
                orthogonalCutNodes(child, true); // child may be cut
            final List<Set<BiTreeNode<Pair<Position, TRSTerm>>>> next = new ArrayList<>();

            for (final var partial : acc) {
                for (final var choice : childChoices) {
                    final Set<BiTreeNode<Pair<Position, TRSTerm>>> u = new HashSet<>(partial);
                    u.addAll(choice);
                    next.add(u);
                }
            }
            acc = next;
        }

        res.addAll(acc);
        return res;
    }

    // ================================================================================
    // Proof
    // ================================================================================

    public static class SASTLoopFinderProof extends Proof.DefaultProof {

        final ImmutableList<Pair<Position, Rule>> rewriteSeq;

        final NonTerminationProbProofNode loopTree;

        final boolean isMaxValueAllCounts;

        int disproveID; // ID of the list element in the nonTerminationProofNode that disproves AST

        public SASTLoopFinderProof(final NonTerminationProbProofNode tree,
            final ImmutableList<Pair<Position, Rule>> rewriteSeq,
            final boolean isMaxValueAllCounts) {
            this.loopTree = tree;
            this.rewriteSeq = rewriteSeq;
            this.isMaxValueAllCounts = isMaxValueAllCounts;

            for (int i = 0; i < this.loopTree.getValue().z.size(); i++) {
                if (isMaxValueAllCounts) {
                    if (this.loopTree.getValue().z.get(i).z.getKey().compareTo(BigFraction.ONE) >= 0
                        || this.loopTree.getValue().z.get(i).z.getValue().compareTo(BigFraction.ONE) >= 0) {
                        this.disproveID = i;
                        break;
                    }
                } else {
                    if (this.loopTree.getValue().z.get(i).z.getKey().compareTo(BigFraction.ONE) >= 0
                        || this.loopTree.getValue().z.get(i).z.getValue().compareTo(BigFraction.ONE) >= 0) {
                        this.disproveID = i;
                        break;
                    }
                }
            }
        }

        @Override
        public String
            export(final Export_Util o,
                final VerbosityLevel level) {
            final StringBuilder sb = new StringBuilder();
            final boolean hasPumpingSub = this.loopTree.getValue().getZ().get(this.disproveID).getY() != null;

            sb.append("We are able to disprove SAST via [IJCAR'26].")
                .append(o.linebreak())
                .append(o.newline());

            if (!hasPumpingSub) {
                if(loopTree.getValue().getZ().get(this.disproveID).getX().isLinear()) { //Linear term
                    sb.append("We use [Thm.11] and count the linear term:")
                        .append(o.linebreak())
                        .append(this.loopTree.getValue().getZ().get(this.disproveID).getX());
                } else if(loopTree.isMaxValueAllCounts()) { //NVD tree
                    sb.append("We use [Thm.15] on a tree that is NVD and count the term:")
                    .append(o.linebreak())
                    .append(this.loopTree.getValue().getZ().get(this.disproveID).getX());
                } else { //Orthogonal counts
                    sb.append("We use [Thm.17] and count the following term at orthogonal positions:")
                    .append(o.linebreak())
                    .append(this.loopTree.getValue().getZ().get(this.disproveID).getX());
                }
                
            } else {
                sb.append("We use [Thm.28] and count the pumping substitution:")
                    .append(o.linebreak())
                    .append(this.loopTree.getValue().getZ().get(this.disproveID).getY())
                    .append(o.linebreak())
                    .append(o.newline())
                    .append("Within the baseterm:")
                    .append(o.linebreak())
                    .append(this.loopTree.getValue().getZ().get(this.disproveID).getX());
            }

            final List<Integer> path = new ArrayList<>();
            path.add(1);

            sb.append(o.linebreak())
                .append(o.newline())
                .append("Rewrite sequence tree:")
                .append(o.linebreak())
                .append(this.loopTree.toTreeString("", this.disproveID, this.isMaxValueAllCounts, path, o));

            return sb.toString();
        }
    }

    // ================================================================================
    // Arguments
    // ================================================================================

    public static class Arguments {

        /**
         * Narrowings Steps in "Pre-Processing"
         */
        public int NARROWING = 3;

        /**
         * If true, the full proof is shown with every detail. Otherwise,
         * intermediate steps are omitted.
         */
        public boolean FULLPROOF = false;

        /**
         * The maximum number of iterations the processor should make during loop generation.
         */
        public int MAXITERATIONSLOOP = -1; // less than 1 --> infinity iterations

        /**
         * The maximum number of iterations the processor should make before moving to the next term.
         */
        public int MAXITERATIONSTREE = 500; // less than 1 --> infinity iterations

        /**
         * Flag to indicate if Forward Narrowing should be used
         */
        public static final boolean F_NARROWING = true;

        /**
         * Flag to indicate if Backward Narrowing should be used
         */
        public static final boolean B_NARROWING = false;

        /**
         * Flag to indicate if narrowing into variables is permitted
         */
        public static final boolean ALLOWVARPOS = false;

        /**
         * Flag to indicate if searching for all (orthogonal) cuts is permitted
         */
        public boolean allcuts = false;
    }

}
