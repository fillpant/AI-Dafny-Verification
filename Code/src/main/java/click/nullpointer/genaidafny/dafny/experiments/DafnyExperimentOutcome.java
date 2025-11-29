package click.nullpointer.genaidafny.dafny.experiments;

public enum DafnyExperimentOutcome {
    /**
     * Experiment succeeded.
     */
    SUCCESS,
    /**
     * Experiment failed/terminated prematurely due to an internal error (code-related).
     */
    FAILURE_INTERNAL_ERROR,
    /**
     * Experiment reached the verification stage at least once, but nonetheless failed.
     */
    FAILURE_VERIFY,
    /**
     * Experiment failed before reaching the verification stage at all.
     */
    FAILURE_RESOLVE;

}
