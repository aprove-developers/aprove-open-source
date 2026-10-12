package aprove.verification.dpframework.DPConstraints;

import java.util.*;

import aprove.verification.dpframework.BasicStructures.*;

/**
 * Checks constraints for a bijective renaming of their variables, comparing
 * constraint sets in iteration order. This does not define a total ordering.
 */
public class ConstraintComparator {

    // The private comparison methods return 0 for a match and nonzero otherwise.

    /**
     * The renaming built up while two constraints are compared. One renaming
     * is used for the whole constraints.
     */
    private static class Renaming {
        private final Map<TRSVariable, TRSVariable> forward = new LinkedHashMap<TRSVariable, TRSVariable>();
        private final Map<TRSVariable, TRSVariable> backward = new LinkedHashMap<TRSVariable, TRSVariable>();
    }

    private int getHash(Constraint o) {
        if (o.isPredicate()) {
            return 1;
        }
        if (o.isReducesTo()) {
            return 2;
        }
        if (o.isImplication()) {
            return 3;
        }
        if (o.isConstraintSet()) {
            return 4;
        }
        return 0;
    }

    private int compareSS(ConstraintSet o1, ConstraintSet o2, Renaming map) {
        int h = o1.size() - o2.size();
        if (h == 0) {
            Iterator<Constraint> it1 = o1.iterator();
            Iterator<Constraint> it2 = o2.iterator();
            while (h == 0 && it1.hasNext()) {
                h = this.compareCC(it1.next(), it2.next(), map);
            }
        }
        return h;
    }

    private int compareII(Implication o1, Implication o2, Renaming map) {
        int l = o1.getQuantor().size();
        int h = l - o2.getQuantor().size();
        if (l != 0) {
            throw new RuntimeException("Comparator: Quantors are not empty " + o1.getQuantor());
        }
        if (h == 0) {
            h = this.compareSS(o1.getConditions(), o2.getConditions(), map);
        }
        if (h == 0) {
            h = this.compareCC(o1.getConclusion(), o2.getConclusion(), map);
        }
        return h;
    }

    private int compareAA(TermAtom o1, TermAtom o2, Renaming map) {
        if (o1.isPredicate() && !this.samePredicateAttributes((Predicate) o1, (Predicate) o2)) {
            return 1;
        }
        int h = this.compareTT(o1.getLeft(), o2.getLeft(), map);
        if (h == 0) {
            h = this.compareTT(o1.getRight(), o2.getRight(), map);
        }
        return h;
    }

    /**
     * Compares the attributes that the polynomial encoding uses besides the
     * terms: the kind of the relation, the rule (for its strictness) and the
     * usable rule dependencies.
     */
    private boolean samePredicateAttributes(final Predicate p1, final Predicate p2) {
        return p1.getKind() == p2.getKind()
            && Objects.equals(p1.getOrigRule(), p2.getOrigRule())
            && p1.getULeft() == p2.getULeft()
            && p1.getURight() == p2.getURight();
    }

    private int compareFF(TRSFunctionApplication o1, TRSFunctionApplication o2, Renaming map) {
        int h = o1.getRootSymbol().equals(o2.getRootSymbol()) ? 0 : 1;
        for (int i = 0; h == 0 && i < o1.getArguments().size(); i++) {
            h = this.compareTT(o1.getArgument(i), o2.getArgument(i), map);
        }
        return h;
    }

    private int compareTT(TRSTerm o1, TRSTerm o2, Renaming map) {
        if (o1.isVariable() && o2.isVariable()) {
            final TRSVariable v1 = (TRSVariable) o1;
            final TRSVariable v2 = (TRSVariable) o2;
            final TRSVariable image = map.forward.get(v1);
            final TRSVariable preimage = map.backward.get(v2);
            if (image == null && preimage == null) {
                map.forward.put(v1, v2);
                map.backward.put(v2, v1);
                return 0;
            }
            if (v2.equals(image) && v1.equals(preimage)) {
                return 0;
            }
            return 1;
        }
        if (!o1.isVariable() && !o2.isVariable()) {
            return this.compareFF((TRSFunctionApplication) o1, (TRSFunctionApplication) o2, map);
        }
        return o1.isVariable() ? -1 : 1;
    }

    private int compareCC(Constraint o1, Constraint o2, Renaming map) {
        int l = this.getHash(o1);
        int h = l - this.getHash(o2);
        if (h == 0) {
            switch (l) {
            case 1:
            case 2:
                return this.compareAA((TermAtom) o1, (TermAtom) o2, map);
            case 3:
                return this.compareII((Implication) o1, (Implication) o2, map);
            case 4:
                return this.compareSS((ConstraintSet) o1, (ConstraintSet) o2, map);
            default:
                return o1.equals(o2) ? 0 : 1;
            }
        }
        return h;
    }

    public boolean isRenamingOf(Constraint o1, Constraint o2) {
        return this.compareCC(o1, o2, new Renaming()) == 0;
    }

}
