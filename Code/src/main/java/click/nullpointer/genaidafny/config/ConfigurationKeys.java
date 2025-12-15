package click.nullpointer.genaidafny.config;

import click.nullpointer.genaidafny.openai.completion.common.OpenAITextModel;
import org.apache.commons.cli.Converter;
import org.apache.commons.cli.Option;

public enum ConfigurationKeys {
    DISABLE_EXPERIMENT_CACHE(Option.builder().longOpt("no-prompt-cache").desc("Disable prompt caching per-experiment.").get()),
    FORCE_RERUN_EXPERIMENTS(Option.builder().longOpt("force-rerun").desc("Force re-run of all completed experiments.")
            .get(), null, "Forcing experiment re-run will overwrite previous results."),
    MAX_GEN_AI_INTERACTIONS(Option.builder().longOpt("max-ai-interactions").desc("Max number of interactions between the program and GenAI, in each experiment.").type(Integer.class).hasArg().get(), "10"),
    DO_NOT_PROMPT_CONFIRMATION(Option.builder("y").longOpt("yes").desc("Do not prompt for confirmation though STDIN.").get()),
    INPUT_PROBLEM_FILE(Option.builder("i").longOpt("input-problem-file").desc("Input problem file path.").hasArg().type(String.class).converter(Converter.FILE).get(), "resources/problems.json", null),
    MAX_GEN_AI_OUTPUT_TOKENS(Option.builder().longOpt("max-completion-tokens").desc("Max number of tokens GenAI is allowed to produce in an output before it cuts off (to prevent loong loops)").hasArg().type(Integer.class).get(), "10000"),
    DISABLE_LATEX_REPORT(Option.builder().longOpt("disable-latex-report").desc("Disable latex report creation for experiments.").get()),
    MAX_CONTEXT_MESSAGES_COUNT(Option.builder().longOpt("max-context-cnt").desc("Maximum number of previous messages to send on each GenAI request, for context. WARNING: grows very quickly, and costs.").hasArg().type(Integer.class).get(), Integer.MAX_VALUE + ""),
    GEN_AI_MODEL(Option.builder("m").longOpt("gen-ai-model").desc("The OpenAI model to use for experiments.").hasArg().type(OpenAITextModel.class).get(), OpenAITextModel.GPT_4O_MINI.toString());
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
