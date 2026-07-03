package aprove.api.server;

import java.util.*;

import org.json.*;

import aprove.api.details.*;
import aprove.api.prooftree.*;

/**
 * Thread-safe ProofTreeListener that accumulates all proof tree nodes into a
 * JSON array.  Safe to call from concurrent analysis threads.
 */
class ServerProofListener implements ProofTreeListener {

    private final List<JSONObject> nodes = new ArrayList<>();
    private final IdentityHashMap<ProofTreeNode, Integer> nodeIndex = new IdentityHashMap<>();

    @Override
    public synchronized void createRoot(ProofTreeNode node) {
        register(node);
    }

    @Override
    public synchronized void createChild(ProofTreeNode node) {
        register(node);
    }

    @Override
    public synchronized void createProof(ProofTreeNode node) {
        register(node);
    }

    @Override public synchronized void setTruth(ProofTreeNode node, String truth) {}
    @Override public void setComplexity(ProofTreeNode node, String asymptotic, String concrete) {}
    @Override public void setCertificationState(ProofTreeNode node, CPFCheckResult state) {}

    public synchronized JSONArray toJsonArray() {
        JSONArray arr = new JSONArray();
        for (JSONObject obj : nodes) arr.put(obj);
        return arr;
    }

    private int register(ProofTreeNode node) {
        if (nodeIndex.containsKey(node)) return nodeIndex.get(node);

        int idx = nodes.size();
        nodeIndex.put(node, idx);

        JSONObject obj = new JSONObject();
        obj.put("index", idx);
        obj.put("parentIndex", parentIndex(node));
        obj.put("obligationName", node.getName());
        obj.put("obligationPlain", plain(node.getDetail(Capability.PLAIN)));

        node.getProof().ifPresentOrElse(
            proof -> {
                obj.put("processorName", proof.getName());
                obj.put("implication",   proof.getImplication());
                obj.put("proof",         plain(proof.getDetail(Capability.PLAIN)));
            },
            () -> {
                obj.put("processorName", JSONObject.NULL);
                obj.put("implication",   JSONObject.NULL);
                obj.put("proof",         JSONObject.NULL);
            }
        );

        nodes.add(obj);
        return idx;
    }

    private Object parentIndex(ProofTreeNode node) {
        return node.getParent()
                   .map(p -> (Object) nodeIndex.getOrDefault(p, -1))
                   .orElse(JSONObject.NULL);
    }

    private static String plain(Detail detail) {
        return detail.getDetailString().orElse("");
    }
}
