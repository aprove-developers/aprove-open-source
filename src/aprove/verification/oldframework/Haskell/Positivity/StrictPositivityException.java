package aprove.verification.oldframework.Haskell.Positivity;

import aprove.input.Generated.haskell.node.*;

/**
 * Thrown if a Haskell program declares a data type that is not strictly positive.
 */
public class StrictPositivityException extends RuntimeException {

    private static final long serialVersionUID = 4370926018563493276L;

    /** Token of the first offending declaration, may be {@code null}. */
    private final transient Token token;

    /**
     * @param token token of the first offending declaration, may be {@code null}
     * @param message description of all violations
     */
    public StrictPositivityException(final Token token, final String message) {
        super(message);
        this.token = token;
    }

    /**
     * @return token of the first offending declaration, may be {@code null}
     */
    public Token getToken() {
        return this.token;
    }
}
