package aprove.api.prooftree.impl;

import java.nio.file.*;
import java.util.*;

import aprove.api.impl.*;
import aprove.api.prooftree.*;
import aprove.cli.*;
import aprove.exit.*;
import aprove.prooftree.Obligations.*;
import aprove.runtime.*;
import aprove.strategies.Parameters.*;
import aprove.verification.oldframework.Input.*;

public enum AproveBuilder {
    ;

    @FunctionalInterface
    public interface AProVEFactory {
        AProVE create(Optional<Path> onlineCertificationPath,
                      boolean onlyCertifiableTechniquesIfPossible,
                      Optional<Strategy> strategy,
                      Timeout timeout) throws SourceException, KillAproveException, IllegalArgumentException;
    }

    public static AProVE createAprove(AnalyzableProblemInputImpl analyzableProblemInput,
                                      Optional<Path> onlineCertificationPath,
                                      boolean onlyCertifiableTechniquesIfPossible,
                                      Optional<Strategy> strategy,
                                      Timeout timeout) throws SourceException,
                                                       KillAproveException,
                                                       IllegalArgumentException {
        CertificationHandler.onlineCertificationPath(onlineCertificationPath);
        CertificationHandler.setOnlineChecker(analyzableProblemInput.getProblemInput().getCPFOnlineCheckerPrefix());
        Input input = analyzableProblemInput.createInput();
        return createAproveFromInput(input, onlyCertifiableTechniquesIfPossible, strategy, timeout);
    }

    public static AProVE createAproveFromObligation(BasicObligation obligation,
                                                     Language language,
                                                     String name,
                                                     Optional<Path> onlineCertificationPath,
                                                     boolean onlyCertifiableTechniquesIfPossible,
                                                     Optional<Strategy> strategy,
                                                     Timeout timeout) throws KillAproveException,
                                                                      IllegalArgumentException {
        CertificationHandler.onlineCertificationPath(onlineCertificationPath);
        CertificationHandler.setOnlineChecker(name);
        AProVE aprove = new AProVE(obligation, language, name);
        StrategyProgram sp = getStrategy(aprove, onlyCertifiableTechniquesIfPossible, strategy);
        if (sp != null) {
            aprove.setStrategy(sp);
        }
        if (!timeout.isInfinite()) {
            aprove.setTimeout(timeout.getDurationOrThrow());
        }
        return aprove;
    }

    private static AProVE createAproveFromInput(Input input,
                                                boolean onlyCertifiableTechniquesIfPossible,
                                                Optional<Strategy> suggestedStrategy,
                                                Timeout timeout) throws SourceException,
                                                                 KillAproveException,
                                                                 IllegalArgumentException {
        AProVE aprove = new AProVE(input);
        StrategyProgram strategy = getStrategy(aprove, onlyCertifiableTechniquesIfPossible, suggestedStrategy);
        if (strategy != null) {
            aprove.setStrategy(strategy);
        }
        if (!timeout.isInfinite()) {
            aprove.setTimeout(timeout.getDurationOrThrow());
        }
        return aprove;
    }

    private static StrategyProgram getStrategy(AProVE aprove,
                                               boolean onlyCertifiableTechniquesIfPossible,
                                               Optional<Strategy> suggestedStrategy) throws KillAproveException,
                                                                                     IllegalArgumentException {
        if (suggestedStrategy.isPresent() && onlyCertifiableTechniquesIfPossible) {
            throw new IllegalArgumentException("You cannot do both: Choose a strategy and require the usage of certifiable techniques.");
        } else if (suggestedStrategy.isPresent()) {
            StrategyProgram result = doGetStrategy(suggestedStrategy.get());
            if (Options.performEagerChecking) {
                result.eagerCheck();
            }
            Options.certifier = Certifier.NONE;
            return result;
        } else if (onlyCertifiableTechniquesIfPossible && aprove.getRoot().offersCertifiableTechniques()) {
            Options.certifier = Certifier.CETA;
            return StrategyTranslator.strategyFromModule(Certifier.CETA.getDefaultStrategyName());
        } else {
            Options.certifier = Certifier.NONE;
            return null;
        }
    }

    private static StrategyProgram doGetStrategy(Strategy strategy) {
        if (strategy.isModuleName()) {
            return StrategyTranslator.strategyFromModule(strategy.getText());
        } else {
            return StrategyTranslator.strategy(strategy.getText());
        }
    }
}
