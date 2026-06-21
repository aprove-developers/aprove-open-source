package aprove.api.prooftree.impl;

import java.util.*;

import aprove.api.prooftree.*;
import aprove.runtime.*;

public class ProveRunnerExecutor implements Runnable {

    public static void execute(ProofTreeOperationManager operationManager,
                               ProveRunner runner,
                               ProofResultHandler proofResultHandler,
                               Runnable onFinish) {
        new Thread(new ProveRunnerExecutor(operationManager, runner, proofResultHandler, onFinish)).start();
    }

    private final ProofTreeOperationManager operationManager;
    private final ProveRunner runner;
    private final ProofResultHandler proofResultHandler;
    private final Runnable onFinish;

    public ProveRunnerExecutor(ProofTreeOperationManager operationManager,
                               ProveRunner runner,
                               ProofResultHandler proofResultHandler,
                               Runnable onFinish) {
        this.operationManager = operationManager;
        this.runner = runner;
        this.proofResultHandler = proofResultHandler;
        this.onFinish = onFinish;
    }

    @Override
    public void run() {
        try {
            proofResultHandler.onRun(operationManager);
            if (doRun()) {
                proofResultHandler.onTimeout(operationManager);
            } else {
                proofResultHandler.onSuccess(operationManager, getMessage());
            }
        } catch (RuntimeException e) {
            proofResultHandler.onError(operationManager, e);
            e.printStackTrace();
        }
    }

    private boolean doRun() {
        try {
            return this.runner.run();
        } finally {
            // onFinish should be executed before the proof result handler is triggered
            onFinish.run();
        }
    }

    private String getMessage() {
        return this.runner.getRoot().getTruthValue().toWstString();
    }
}
