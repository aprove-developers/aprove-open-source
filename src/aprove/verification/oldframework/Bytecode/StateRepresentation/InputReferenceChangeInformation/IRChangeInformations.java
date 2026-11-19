package aprove.verification.oldframework.Bytecode.StateRepresentation.InputReferenceChangeInformation;

import java.util.ConcurrentModificationException;
import java.util.EnumMap;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;
import java.util.Map.Entry;
import java.util.function.BiFunction;
import java.util.function.UnaryOperator;

import aprove.verification.oldframework.Bytecode.Merger.*;
import aprove.verification.oldframework.Bytecode.Parser.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.*;
import aprove.verification.oldframework.Bytecode.StateRepresentation.InputReferenceChangeInformation.IrChangeInformation.*;
import aprove.verification.oldframework.Utility.GenericStructures.*;

public class IRChangeInformations implements Iterable<IrChangeInformation> {

    /*
     * these are part of a more detailed frontend analysis that was originally planned but later scrapped.
     * currently it would be enough to only use abstractedReachableChanges,
     * as the more detailed information gained by storing local changes explicitly is never used.
     *
     * The summariseAllChanges combines local and reachable changes, and is currently the only way information from here is used.
     */
    private Map<FieldIdentifier, IrChangeInformation> localFieldChanges;
    private IrChangeInformation localArrayChanges;

    private EnumMap<IrChangeInformation.ChangeType, IrChangeInformation> abstractedReachableChanges;

    /**
     * create empty change information
     */
    public IRChangeInformations() {
        this.localFieldChanges = new HashMap<>();
        this.abstractedReachableChanges = new EnumMap<>(IrChangeInformation.ChangeType.class);
    }

    protected IRChangeInformations(IRChangeInformations original) {
        this.localFieldChanges = new HashMap<>(original.localFieldChanges);
        this.localArrayChanges = original.localArrayChanges;
        this.abstractedReachableChanges = new EnumMap<>(original.abstractedReachableChanges);
    }

    /**
     * @return the most general change information
     */
    public static IRChangeInformations unknownChange() {
        IRChangeInformations res = new IRChangeInformations();
        res.abstractedReachableChanges.put(ChangeType.ADDRESS, IrAddressChangeInformation.UNKNOWN);
        res.abstractedReachableChanges.put(ChangeType.INTEGER, IrPrimitiveChangeInformation.UNKNOWN_INT);
        res.abstractedReachableChanges.put(ChangeType.FLOAT, IrPrimitiveChangeInformation.UNKNOWN_FLOAT);
        return res;
    }

    public IRChangeInformations copy() {
        return new IRChangeInformations(this);
    }

    public void clear() {
        localFieldChanges.clear();
        localArrayChanges = null;
        abstractedReachableChanges.clear();
    }

    public boolean changed() {
        return !localFieldChanges.isEmpty()
                || localArrayChanges != null
                || !abstractedReachableChanges.isEmpty();
    }

    public boolean merge(IRChangeInformations other) {
        return merge(other, null);
    }

    /**
     * merge two IRChangeInformations, that may use different variable names.
     * @param other
     * @param varCache the cache that maps variables in one change information to variables in the other, may be null
     * @return
     */
    public boolean merge(IRChangeInformations other, VariableCache varCache) {
        boolean changed = false;
        for(Entry<FieldIdentifier, IrChangeInformation> entry : other.localFieldChanges.entrySet()) {
            changed |= mergeLocalChange(entry.getValue(), entry.getKey(), varCache);
        }
        if (varCache != null) { //rename when varCache exists and info does not exist in other
            for(Entry<FieldIdentifier, IrChangeInformation> entry : this.localFieldChanges.entrySet()) {
                if (!other.localFieldChanges.containsKey(entry.getKey())) {
                    entry.setValue(entry.getValue().replaceReference(varCache, true));
                }
            }
        }
        if (other.localArrayChanges != null) {
            changed |= addLocalChange(other.localArrayChanges, varCache);
        } else if (varCache != null && this.localArrayChanges != null) { //rename when varCache exists and info does not exist in other
            this.localArrayChanges = this.localArrayChanges.replaceReference(varCache, true);
        }
        for (IrChangeInformation reachableChange : other.abstractedReachableChanges.values()) {
            changed |= addReachableChange(reachableChange, varCache);
        }
        if (varCache != null) { //rename when varCache exists and info does not exist in other
            for(Entry<ChangeType, IrChangeInformation> entry : this.abstractedReachableChanges.entrySet()) {
                if (!other.abstractedReachableChanges.containsKey(entry.getKey())) {
                    entry.setValue(entry.getValue().replaceReference(varCache, true));
                }
            }
        }
        return changed;
    }

    /**
     * Add a local change, overwriting old information
     * @param change
     * @param field
     */
    public void putLocalChange(IrChangeInformation change, FieldIdentifier field) {
        if (field == null) {
            addLocalChange(change, null);
        } else {
            localFieldChanges.put(field, change);
        }
    }

    /**
     * Merge local changes
     * @param change
     * @param field
     * @param varCache may be null
     * @return
     */
    public boolean mergeLocalChange(IrChangeInformation change, FieldIdentifier field, VariableCache varCache) {
        if (field == null) {
            return addLocalChange(change, varCache);
        } else {
            IrChangeInformation old = localFieldChanges.get(field);
            if (old == null) {
                if (varCache != null) {
                    change = change.replaceReference(varCache, false);
                }
                localFieldChanges.put(field, change);
                return true;
            } else {
                IrChangeInformation merged = old.merge(change, varCache);
                if (merged == old) {
                    return false;
                } else {
                    localFieldChanges.put(field, old.merge(change, varCache));
                    return true;
                }
            }
        }
    }

    /**
     * Adds a local array change, merging with existing information
     * @param change
     * @param varCache may be null
     * @return
     */
    public boolean addLocalChange(IrChangeInformation change, VariableCache varCache) {
        if (localArrayChanges == null) {
            if (varCache != null) {
                change = change.replaceReference(varCache, false);
            }
            localArrayChanges = change;
            return true;
        }
        IrChangeInformation merged = localArrayChanges.merge(change, varCache);
        assert merged != null;
        if (merged == localArrayChanges) {
            return false;
        } else {
            localArrayChanges = merged;
            return true;
        }
    }

    /**
     * Add a reachable change, merging with existing information
     * @param change
     * @param varCache may be null
     * @return
     */
    public boolean addReachableChange(IrChangeInformation change, VariableCache varCache) {
        IrChangeInformation old = abstractedReachableChanges.get(change.getChangeType());
        if (old == null) {
            if (varCache != null) {
                change = change.replaceReference(varCache, false);
            }
            abstractedReachableChanges.put(change.getChangeType(), change);
            return true;
        } else {
            IrChangeInformation merged = old.merge(change, varCache);
            assert merged != null;
            if (merged == old) {
                return false;
            } else {
                abstractedReachableChanges.put(change.getChangeType(), merged);
                return true;
            }
        }
    }

    public boolean containsChanges(IRChangeInformations other, BiFunction<AbstractVariableReference, AbstractVariableReference, Boolean> varComparator) {
        for (Entry<FieldIdentifier, IrChangeInformation> entry : other.localFieldChanges.entrySet()) {
            IrChangeInformation thisChange = localFieldChanges.get(entry.getKey());
            if (thisChange == null || !thisChange.containsChange(entry.getValue(), varComparator)) {
                return false;
            }
        }
        if (other.localArrayChanges != null &&
                (this.localArrayChanges == null || !this.localArrayChanges.containsChange(other.localArrayChanges, varComparator))) {
            return false;
        }
        for (Entry<IrChangeInformation.ChangeType, IrChangeInformation> entry : other.abstractedReachableChanges.entrySet()) {
            IrChangeInformation thisChange = abstractedReachableChanges.get(entry.getKey());
            if (thisChange == null || !thisChange.containsChange(entry.getValue(), varComparator)) {
                return false;
            }
        }
        return true;
    }

    public boolean containsChanges(IRChangeInformations other) {
        return containsChanges(other, (var1, var2) -> var1 == var2);
    }

    /**
     * Combines local and reachable changes
     */
    public EnumMap<ChangeType, IrChangeInformation> summariseAllChanges() {
        IRChangeInformations res = new IRChangeInformations();
        for (IrChangeInformation change : this) {
            res.addReachableChange(change, null);
        }
        return res.abstractedReachableChanges;
    }

    public void replaceReference(AbstractVariableReference oldRef, AbstractVariableReference newRef) {
        this.replaceAll(change -> change.replaceReference(oldRef, newRef));
    }

    public IRChangeInformations asChangesFromLowerFrame(BidirectionalMap<AbstractVariableReference, AbstractVariableReference> endingToRenamedEnding) {
        IRChangeInformations res = this.copy();
        res.replaceAll(change -> change.replaceReference(endingToRenamedEnding::getRL).asChangeFromLowerFrame());
        return res;
    }

    public void replaceAll(UnaryOperator<IrChangeInformation> replacer) {
        localFieldChanges.replaceAll((field, change) -> replacer.apply(change));
        if (localArrayChanges != null)
            localArrayChanges = replacer.apply(localArrayChanges);
        abstractedReachableChanges.replaceAll((type, change) -> replacer.apply(change));
    }

    @Override
    public int hashCode() {
        final int prime = 31;
        int result = 1;
        result = prime * result + ((abstractedReachableChanges == null) ? 0 : abstractedReachableChanges.hashCode());
        result = prime * result + ((localArrayChanges == null) ? 0 : localArrayChanges.hashCode());
        result = prime * result + ((localFieldChanges == null) ? 0 : localFieldChanges.hashCode());
        return result;
    }

    @Override
    public boolean equals(Object obj) {
        if (this == obj)
            return true;
        if (obj == null)
            return false;
        if (getClass() != obj.getClass())
            return false;
        IRChangeInformations other = (IRChangeInformations) obj;
        if (abstractedReachableChanges == null) {
            if (other.abstractedReachableChanges != null)
                return false;
        } else if (!abstractedReachableChanges.equals(other.abstractedReachableChanges))
            return false;
        if (localArrayChanges == null) {
            if (other.localArrayChanges != null)
                return false;
        } else if (!localArrayChanges.equals(other.localArrayChanges))
            return false;
        if (localFieldChanges == null) {
            if (other.localFieldChanges != null)
                return false;
        } else if (!localFieldChanges.equals(other.localFieldChanges))
            return false;
        return true;
    }

    @Override
    public String toString() {
        return  "["
              + (localFieldChanges.isEmpty()          ? "" : "localChanges=" + localFieldChanges)
              + (localArrayChanges == null            ? "" : "localChanges=" + localArrayChanges)
              + (abstractedReachableChanges.isEmpty() ? "" : "reachableChanges=" + abstractedReachableChanges)
              + "]";
    }

    @Override
    public Iterator<IrChangeInformation> iterator() {
        return new Iterator<IrChangeInformation>() {
            Iterator<IrChangeInformation> locaFieldIterator = localFieldChanges.values().iterator();
            IrChangeInformation arrayChanges = localArrayChanges;
            Iterator<IrChangeInformation> reachableChangesIterator = abstractedReachableChanges.values().iterator();

            @Override
            public boolean hasNext() {
                return locaFieldIterator.hasNext() || arrayChanges != null || reachableChangesIterator.hasNext();
            }

            @Override
            public IrChangeInformation next() {
                if (locaFieldIterator.hasNext())
                    return locaFieldIterator.next();
                if (arrayChanges != null) {
                    if (arrayChanges.equals(localArrayChanges)) {
                        arrayChanges = null;
                        return localArrayChanges;
                    } else
                        throw new ConcurrentModificationException();
                }
                return reachableChangesIterator.next();
            }
        };
    }
}
