package aprove.api.prooftree.impl;

import java.nio.file.*;
import java.util.*;

import aprove.api.prooftree.*;
import aprove.api.prooftree.ProofTreeBuilder.*;
import aprove.exit.*;
import aprove.verification.oldframework.Input.*;

public class ProofTreeBuilderImpl implements
                                  ProofTreeBuilder,
                                  BeforeOnlyCertifiableTechniquesIfPossible,
                                  BeforeStrategy,
                                  BeforeTimeout,
                                  BeforeListener,
                                  BeforeConstruct {

    private static final ProofTreeListener NO_OP_LISTENER = new ProofTreeListener() {
        @Override public void createRoot(ProofTreeNode n) {}
        @Override public void createChild(ProofTreeNode n) {}
        @Override public void createProof(ProofTreeNode n) {}
        @Override public void setTruth(ProofTreeNode n, String t) {}
        @Override public void setComplexity(ProofTreeNode n, String a, String c) {}
        @Override public void setCertificationState(ProofTreeNode n, CPFCheckResult s) {}
    };

    private final AproveBuilder.AProVEFactory aproveFactory;
    private Optional<Path> onlineCertificationPath;
    private boolean onlyCertifiableTechniquesIfPossible;
    private Optional<Strategy> strategy;
    private Timeout timeout;
    private ProofTreeListener proofTreeListener = NO_OP_LISTENER;

    public ProofTreeBuilderImpl(AproveBuilder.AProVEFactory aproveFactory) {
        this.aproveFactory = aproveFactory;
    }

    @Override
    public BeforeOnlyCertifiableTechniquesIfPossible onlineCertificationPath(Optional<Path> onlineCertificationPath) {
        Objects.requireNonNull(onlineCertificationPath);
        this.onlineCertificationPath = onlineCertificationPath;
        return this;
    }

    @Override
    public BeforeStrategy onlyCertifiableTechniquesIfPossible(boolean onlyCertifiableTechniquesIfPossible) {
        this.onlyCertifiableTechniquesIfPossible = onlyCertifiableTechniquesIfPossible;
        return this;
    }

    @Override
    public BeforeTimeout strategy(Optional<Strategy> strategy) {
        Objects.requireNonNull(strategy);
        this.strategy = strategy;
        return this;
    }

    @Override
    public BeforeListener timeout(Timeout timeout) {
        Objects.requireNonNull(timeout);
        this.timeout = timeout;
        return this;
    }

    @Override
    public BeforeConstruct listener(ProofTreeListener proofTreeListener) {
        Objects.requireNonNull(proofTreeListener);
        this.proofTreeListener = proofTreeListener;
        return this;
    }

    @Override
    public ProofTree construct() throws ProofTreeInstantiationException {
        try {
            return ProofTreeImpl.from(proofTreeListener,
                                      aproveFactory.create(onlineCertificationPath,
                                                           onlyCertifiableTechniquesIfPossible,
                                                           strategy,
                                                           timeout));
        } catch (SourceException | KillAproveException | IllegalArgumentException e) {
            throw new ProofTreeInstantiationException("unable to instantiate the proof tree", e);
        }
    }
}
