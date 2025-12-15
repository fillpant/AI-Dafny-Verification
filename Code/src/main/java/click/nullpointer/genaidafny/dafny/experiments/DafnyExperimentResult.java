package click.nullpointer.genaidafny.dafny.experiments;

import click.nullpointer.genaidafny.common.utils.EventTimer;

public record DafnyExperimentResult(DafnyExperimentOutcome outcome, int verificationAttempts, int resolutionAttempts, int softFailedResolutions, int hardFailedResolutions,int responsesWithAssume, EventTimer experimentTimings) {
}
