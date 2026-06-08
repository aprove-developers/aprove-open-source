package aprove.verification.probabilistic.BasicStructures;

import java.util.*;
import java.util.stream.*;

import org.apache.commons.math3.fraction.*;

import aprove.prooftree.Export.Utility.*;
import aprove.verification.dpframework.BasicStructures.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class NonTerminationProbProofNode extends TreeNode<ProofNodeContent> {

    //The parent Node
    private NonTerminationProbProofNode parent;
    //You can take one of the options for the proof against Termination
    //But we have save all possibilities and compute them further
    private final List<List<NonTerminationProbProofNode>> rewriteOptions = new ArrayList<>();
    //So we know in which option a child is
    private final Map<NonTerminationProbProofNode, List<NonTerminationProbProofNode>> childToOption = new HashMap<>();
    //The Depth of the Tree
    private int treeDepth = 0;
    //The set of values, which are calculated through the children
    private final Set<Integer> valueThroughChildren = new HashSet<>();
    //Boolean that states whether it may still be possible to reach the looping term.
    //Once false, this remains false.
    private boolean isPossibleToReachLoop = true;

    public NonTerminationProbProofNode(final ProofNodeContent value) {
        super(value);
    }

    public boolean isPossibleToReachLoop() {
        return this.isPossibleToReachLoop;
    }

    public void setPossibleToReachLoop(final boolean isPossibleToReachLoop) {
        this.isPossibleToReachLoop = isPossibleToReachLoop;
    }

    /**
     * Adds a new rewrite option consisting of the given nodes to the current node's rewrite options.
     * After adding the new rewrite option, the values are re-evaluated.
     *
     * @param nodes the list of NonTerminationProofNodes to be added as a new rewrite option
     */

    public void addNewRewriteOption(final List<NonTerminationProbProofNode> nodes) {
        final List<NonTerminationProbProofNode> option = new ArrayList<>();
        //Save the parent of the nodes and in which option the node are
        for (final NonTerminationProbProofNode node : nodes) {
            node.parent = this;
            option.add(node);
            this.childToOption.put(node, option);
        }

        //Only add option if option is not the empty List
        if (!option.isEmpty()) {
            //If rewrite Options is empty we add a new Layer so the Depth is increased
            if (this.rewriteOptions.isEmpty()) {
                increaseDepth();
            }
            this.rewriteOptions.add(option);

            //We need to check if the values are now higher
            computeValuesFromLastChildren();
        }

    }

    /**
     * Computes the values from the last added rewrite option
     */

    private void computeValuesFromLastChildren() {
        final List<Integer> allValues = new ArrayList<>();
        for (Integer i = 0; i < this.value.z.size(); i++) {
            allValues.add(i);
        }
        //We just give a child of the last rewriteOption so we can use the existing Method
        computeValuesFromChildren(allValues, this.rewriteOptions.get(this.rewriteOptions.size() - 1).get(0));
    }

    /**
     * Computes the values that have changed in the rewrite option containing the updated child,
     * and updates the value if the new value is higher than the current one.
     * If any values have been updated, the changes are propagated upwards to the parent node.
     *
     * @param updateValues the list of indices representing the values that have changed
     * @param updatedChild the child that has changed, used to compute the corresponding rewrite option
     */
    private void computeValuesFromChildren(final List<Integer> updateValues, final NonTerminationProbProofNode updatedChild) {
        final List<Integer> changed = new ArrayList<>();

        // Get the Option that contains the child
        final List<NonTerminationProbProofNode> relevantOption = this.childToOption.get(updatedChild);

        for (final Integer i : updateValues) {
            BigFraction sumAllCount = BigFraction.ZERO;
            BigFraction sumOrthoCount = BigFraction.ZERO;

            for (final NonTerminationProbProofNode child : relevantOption) {
                final Triple<TRSTerm, TRSSubstitution, Pair<BigFraction, BigFraction>> temp = child.getValue().getZ().get(i);

                final Pair<BigFraction, BigFraction> valPair = temp.getZ();

                final BigFraction allCounts = valPair.getKey();
                if (allCounts.compareTo(BigFraction.ZERO) < 0 || sumAllCount.equals(BigFraction.MINUS_ONE)) {
                    //Value less than 0 means that we cannot count, e.g., because the base term is not existent for pattern occurrences
                    sumAllCount = BigFraction.MINUS_ONE;
                } else {
                    sumAllCount = sumAllCount.add(allCounts);
                }

                final BigFraction orthoCounts = valPair.getValue();
                if (orthoCounts.compareTo(BigFraction.ZERO) < 0 || sumOrthoCount.equals(BigFraction.MINUS_ONE)) {
                    //Value less than 0 means that we cannot count, e.g., because the base term is not existent for pattern occurrences
                    sumOrthoCount = BigFraction.MINUS_ONE;
                } else {
                    sumOrthoCount = sumOrthoCount.add(orthoCounts);
                }
            }

            // Check if some value increased
            final BigFraction curAllCount = this.value.z.get(i).getZ().getKey();
            final BigFraction curOrthoCount = this.value.z.get(i).getZ().getValue();
            if (curAllCount.compareTo(sumAllCount) < 0 || curOrthoCount.compareTo(sumOrthoCount) < 0) { // One of the two values increased
                final BigFraction newAllCount = curAllCount.compareTo(sumAllCount) < 0 ? sumAllCount : curAllCount;
                final BigFraction newOrthoCount = curOrthoCount.compareTo(sumOrthoCount) < 0 ? sumOrthoCount : curOrthoCount;
                this.valueThroughChildren.add(i);
                this.value.getZ().get(i).setZ(new Pair<>(newAllCount, newOrthoCount));
                changed.add(i);
            }

        }
        //If some value increased, then propagate the new value one layer up
        if (!changed.isEmpty() && this.parent != null) {
            this.parent.computeValuesFromChildren(changed, this);
        }
    }

    /**
     * Checks whether the value at the specified index is derived from the values of the children.
     *
     * @param i the index of the value to check
     * @return true if the value at index i is computed through child nodes, false otherwise
     */

    public boolean isValueThroughChildren(final int i) {
        return this.valueThroughChildren.contains(i);
    }

    /**
     * Puts all Terms where the potential of nontermination is greater than 0 to the map with the potential   *
     * @param map
     */
    public void collectAllTermsWithZ(final Map<TRSTerm, BigFraction> map) {
        //Potenzial für Nichtterminierung
        final BigFraction maxValue = getMaxValue();

        if (maxValue.compareTo(BigFraction.ZERO) > 0) {
            //Wenn der Term potenzial hat
            final TRSTerm term = this.value.getX();
            if (!map.containsKey(term) || maxValue.compareTo(map.get(term)) > 0) {
                //füge ihn hinzu oder aktualisiere ihn wenn Potenzial größer
                map.put(term, maxValue);
            }
        }

        //Mache das auch für alle Kinder
        for (final List<NonTerminationProbProofNode> option : this.rewriteOptions) {
            for (final NonTerminationProbProofNode child : option) {
                child.collectAllTermsWithZ(map);
            }
        }
    }

    /**
     * Collects all leaf nodes at a specific depth level in the tree.
     *
     * @param currentLevel the current depth level during traversal
     * @param targetLevel the target depth level to collect leaves from
     * @param result the list to collect matching leaf nodes
     */
    public void collectLeavesAtLevel(final int currentLevel, final int targetLevel, final List<NonTerminationProbProofNode> result) {
        if (currentLevel == targetLevel && isLeaf()) {
            result.add(this);
            return;
        }

        for (final List<NonTerminationProbProofNode> level : this.rewriteOptions) {
            for (final NonTerminationProbProofNode child : level) {
                child.collectLeavesAtLevel(currentLevel + 1, targetLevel, result);
            }
        }
    }

    /**
     * Increases the depth of the current node by one.
     * If the parent has the same depth, the depth increase is propagated upward.
     */

    private void increaseDepth() {
        this.treeDepth++;
        if (this.parent != null && this.parent.getDepth() == this.treeDepth) {
            this.parent.increaseDepth();
        }

    }

    /**
     * Returns the current depth of this node.
     *
     * @return the depth of this node
     */

    public int getDepth() {
        return this.treeDepth;
    }

    /**
     * Returns the current depth of this node.
     *
     * @return the depth of this node
     */

    public int getDepthWRTParent() {
        if (this.parent == null) {
            return 0;
        } else {
            return this.parent.getDepthWRTParent() + 1;
        }
    }

    /**
     * Returns the maximum value among all values stored in this node.
     *
     * @return the highest BigFraction value in this node
     */

    public BigFraction getMaxValue() {
        BigFraction maxAllCount = this.value.getZ().get(0).getZ().getKey();
        BigFraction maxOrthoCount = this.value.getZ().get(0).getZ().getValue();

        for (int i = 1; i < this.value.z.size(); i++) {
            if (maxAllCount.compareTo(this.value.z.get(i).z.getKey()) < 0) {
                maxAllCount = this.value.z.get(i).z.getKey();
            }
            if (maxOrthoCount.compareTo(this.value.z.get(i).z.getValue()) < 0) {
                maxOrthoCount = this.value.z.get(i).z.getValue();
            }
        }

        if (maxAllCount.compareTo(maxOrthoCount) > 0) {
            return maxAllCount;
        } else {
            return maxOrthoCount;
        }
    }

    /**
     * @return whether the maximum value is stored in the first component (AllCounts)
     * or in the second component (OnlyOrthogonalCounts)
     */

    public boolean isMaxValueAllCounts() {
        BigFraction maxAllCount = this.value.getZ().get(0).getZ().getKey();
        BigFraction maxOrthoCount = this.value.getZ().get(0).getZ().getValue();

        for (int i = 1; i < this.value.z.size(); i++) {
            if (maxAllCount.compareTo(this.value.z.get(i).z.getKey()) < 0) {
                maxAllCount = this.value.z.get(i).z.getKey();
            }
            if (maxOrthoCount.compareTo(this.value.z.get(i).z.getValue()) < 0) {
                maxOrthoCount = this.value.z.get(i).z.getValue();
            }
        }

        return maxAllCount.compareTo(maxOrthoCount) > 0;
    }

    @Override
    public boolean isLeaf() {
        return this.rewriteOptions.isEmpty();
    }

    /**
     * Returns all leaf nodes in the subtree rooted at this node.
     *
     * @return a list containing all leaf nodes
     */
    public List<NonTerminationProbProofNode> getLeaves() {
        final List<NonTerminationProbProofNode> leaves = new ArrayList<>();
        collectLeaves(leaves);
        return leaves;
    }

    public List<List<NonTerminationProbProofNode>> getRewriteOptions() {
        return this.rewriteOptions;
    }

    /**
     * Helper method to collect all leaves in the subtree.
     *
     * @param acc accumulator for leaf nodes
     */
    public void collectLeaves(final List<NonTerminationProbProofNode> acc) {
        if (isLeaf()) {
            acc.add(this);
            return;
        }

        for (final List<NonTerminationProbProofNode> option : this.rewriteOptions) {
            for (final NonTerminationProbProofNode child : option) {
                child.collectLeaves(acc);
            }
        }
    }

    /**
     * remove all children from this node
     */
    public void cut() {
        this.rewriteOptions.clear();
        this.childToOption.clear();
        this.valueThroughChildren.clear();
        this.treeDepth = 0;
    }

    public void onlyPathTo(final NonTerminationProbProofNode loopingLeaf) {
        NonTerminationProbProofNode cur = loopingLeaf;
        NonTerminationProbProofNode prev = loopingLeaf;
        while (cur != null) {
            final List<List<NonTerminationProbProofNode>> curLeaves = cur.getRewriteOptions();
            for (final List<NonTerminationProbProofNode> innerList : curLeaves) {
                for (final NonTerminationProbProofNode curLeaf : innerList) {
                    if (!curLeaf.equals(prev)) {
                        curLeaf.cut();
                    }
                }
            }
            prev = cur;
            cur = cur.parent;
        }
    }

    @Override
    public String toString() {
        return toTreeStringAll();
    }

    public String toTreeString(final String indent, final int i, final boolean isMaxValueAllCounts, final List<Integer> path, final Export_Util o) {
        final StringBuilder sb = new StringBuilder();

        final String pathStr = path.stream()
            .map(String::valueOf)
            .collect(Collectors.joining("."));

        sb.append(o.preFormatted(indent + "[Node: " + pathStr + ", Term: " + this.value.getX() + ", Prob: " + this.value.getY() + "] \n"));

        if (!isValueThroughChildren(i)) {
            return sb.toString();
        }

        // Find child that disproves AST
        List<NonTerminationProbProofNode> bestLevel = null;

        BigFraction maxSum = BigFraction.ZERO;

        for (final List<NonTerminationProbProofNode> level : this.rewriteOptions) {
            BigFraction sum = BigFraction.ZERO;
            if (isMaxValueAllCounts) {
                for (final NonTerminationProbProofNode child : level) {
                    sum = sum.add(child.getValue().getZ().get(i).getZ().getKey()); // Get All Counts
                }
            } else {
                for (final NonTerminationProbProofNode child : level) {
                    sum = sum.add(child.getValue().getZ().get(i).getZ().getValue()); // Get Ortho Counts
                }
            }
            if (maxSum.compareTo(sum) < 0 || (maxSum.equals(sum) && level.get(0).getValue().getZ().get(i).getY() != null)) {
                maxSum = sum;
                bestLevel = level;
            }
        }

        if (bestLevel != null) {
            int num = 1;
            for (final NonTerminationProbProofNode child : bestLevel) {
                final List<Integer> optionPath = new ArrayList<>(path);
                optionPath.add(num);
                sb.append(child.toTreeString(indent + "  ", i, isMaxValueAllCounts, optionPath, o));
                num++;
            }
        }

        return sb.toString();
    }

    public String toTreeStringAll() {
        final List<Integer> initialPath = new ArrayList<>();
        initialPath.add(1);
        return toTreeStringAll("", initialPath);
    }

    private String toTreeStringAll(final String indent, final List<Integer> path) {
        final StringBuilder sb = new StringBuilder();

        final String pathStr = path.stream()
            .map(String::valueOf)
            .collect(Collectors.joining("."));

        sb.append(indent)
            .append("[")
            .append(pathStr)
            .append("] (")
            .append(this.value.getX())
            .append("), ")
            .append(this.value.getY())
            .append(", ")
            .append(this.value.getZ())
            .append(")\n");

        for (int i = 0; i < this.rewriteOptions.size(); i++) {
            final List<NonTerminationProbProofNode> group = this.rewriteOptions.get(i);
            if (group.isEmpty()) {
                continue;
            }

            final List<Integer> optionPath = new ArrayList<>(path);
            optionPath.add(i + 1);
            final String optionStr = optionPath.stream()
                .map(String::valueOf)
                .collect(Collectors.joining("."));

            sb.append(indent)
                .append("  --- Rewrite Option ")
                .append(optionStr)
                .append(" ---\n");

            for (final NonTerminationProbProofNode child : group) {
                sb.append(child.toTreeStringAll(indent + "  ", new ArrayList<>(optionPath)));
            }
        }

        return sb.toString();
    }
}
