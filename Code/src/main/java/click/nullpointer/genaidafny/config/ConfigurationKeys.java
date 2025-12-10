package click.nullpointer.genaidafny.config;

import org.apache.commons.cli.Converter;
import org.apache.commons.cli.Option;

public enum ConfigurationKeys {
    DISABLE_EXPERIMENT_CACHE(Option.builder().longOpt("no-prompt-cache").desc("Disable prompt caching per-experiment.").get()),
    FORCE_RERUN_EXPERIMENTS(Option.builder().longOpt("force-rerun").desc("Force re-run of all completed experiments.")
            .get(), null, "Forcing experiment re-run will overwrite previous results."),
    MAX_GEN_AI_INTERACTIONS(Option.builder().longOpt("max-ai-interactions").desc("Max number of interactions between the program and GenAI, in each experiment.").type(Integer.class).hasArg().get(), "10"),
    DO_NOT_PROMPT_CONFIRMATION(Option.builder("y").longOpt("yes").desc("Do not prompt for confirmation though STDIN.").get()),
    INPUT_PROBLEM_FILE(Option.builder("i").longOpt("input-problem-file").desc("Input problem file path.").hasArg().type(String.class).converter(Converter.FILE).get(), "resources/problems.json", null);
    private final Option option;
    private final String defaultValue;
    private final String confirmationMessage;

    ConfigurationKeys(Option option) {
        this(option, null);
    }

    ConfigurationKeys(Option option, String defaultValue) {
        this(option, defaultValue, null);
    }

    ConfigurationKeys(Option option, String defaultValue, String confirmationMessage) {
        this.option = option;
        this.defaultValue = defaultValue;
        this.confirmationMessage = confirmationMessage;
    }

    public Option getOption() {
        return option;
    }

    public String defaultValue() {
        return defaultValue;
    }

    public boolean requiresConfirmation() {
        return confirmationMessage != null;
    }

    public String getConfirmationMessage() {
        return confirmationMessage;
    }
}
