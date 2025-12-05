package click.nullpointer.genaidafny;

import click.nullpointer.genaidafny.common.utils.Utilities;
import click.nullpointer.genaidafny.config.ConfigurationKeys;
import click.nullpointer.genaidafny.dafny.DafnyProblem;
import click.nullpointer.genaidafny.dafny.experiments.DafnyExperiment;
import click.nullpointer.genaidafny.dafny.experiments.DafnyExperimentResult;
import click.nullpointer.genaidafny.openai.completion.OpenAICompletionManager;
import com.google.gson.Gson;
import org.apache.commons.cli.CommandLine;
import org.apache.commons.cli.CommandLineParser;
import org.apache.commons.cli.DefaultParser;
import org.apache.commons.cli.Options;
import org.apache.commons.cli.ParseException;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.Arrays;
import java.util.Collections;
import java.util.HashMap;
import java.util.Map;
import java.util.Objects;
import java.util.Scanner;
import java.util.function.Function;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Collectors;

public class Main {
    private static final File OPENAI_INTEGRATION_LOG_DIR = new File("openai_promp_logs");
    private static final File EXPERIMENT_LOG_FILE = new File("experiment_logs.log");
    private static final Logger LOG = Utilities.createLogger("Experiment Controller", EXPERIMENT_LOG_FILE);
    private static final File PROBLEM_DATA_DIR = new File("problem_data");
    private static final File PROBLEM_FILE = new File("resources/problems.json");
    private static final Gson GSON = new Gson();
    private static OpenAICompletionManager manager;
    private static Map<ConfigurationKeys, String> config;

    public static void main(String... args) throws IOException {
        config = Collections.unmodifiableMap(Objects.requireNonNull(parseAndConfirmConfiguration(args)));
        LOG.fine("Configuration: " + config.entrySet().stream().map(e -> e.getKey() + (e.getValue() != null ? "=" + e.getValue() : "")).collect(Collectors.joining(",")));
        LOG.info("Initialising OpenAI Integration...");
        manager = new OpenAICompletionManager(System.getenv().get("OPENAI_KEY"), OPENAI_INTEGRATION_LOG_DIR);
        LOG.info("Reading problems...");
        try (FileReader fr = new FileReader(PROBLEM_FILE)) {
            DafnyProblem[] problems = GSON.fromJson(fr, DafnyProblem[].class);
            LOG.info("Found " + problems.length + " problems.");
            if (!validateProblemList(problems)) {
                LOG.severe("Program exiting due to failed validation.");
            }
            processAllProblems(problems);
        }
    }


    private static Map<ConfigurationKeys, String> parseAndConfirmConfiguration(String... args) {
        try {
            CommandLineParser commandLineParser = new DefaultParser();
            Options options = new Options();
            Arrays.stream(ConfigurationKeys.values()).forEach(a -> options.addOption(a.getOption()));
            CommandLine cl = commandLineParser.parse(options, args);

            Map<ConfigurationKeys, String> conf = new HashMap<>();
            Scanner in = new Scanner(System.in);
            for (ConfigurationKeys key : ConfigurationKeys.values()) {
                if (cl.hasOption(key.getOption())) {
                    if (key.requiresConfirmation() && !cl.hasOption(ConfigurationKeys.DO_NOT_PROMPT_CONFIRMATION.getOption())) {
                        boolean confirm = stdinConfirmation(in, key.getConfirmationMessage());
                        if (!confirm) {
                            LOG.warning("Skipping option " + key.getOption().getKey() + " due to non-confirmation.");
                            continue;
                        }
                    }
                    String value = cl.getOptionValue(key.getOption());
                    conf.put(key, value);

                } else {
                    conf.put(key, key.defaultValue());
                }
            }

            return conf;
        } catch (ParseException e) {
            LOG.log(Level.SEVERE, "Failed to parse command line arguments", e);
            return null;
        }
    }

    private static boolean stdinConfirmation(Scanner in, String confirmationMessage) {
        System.out.println(confirmationMessage);
        String input;
        do {
            System.out.print("Continue? [y/N]: ");
            input = in.nextLine();
            if (input.isBlank())
                input = "n";
        } while (!input.equalsIgnoreCase("y") && !input.equalsIgnoreCase("n"));
        return input.equalsIgnoreCase("y");
    }

    private static boolean validateProblemList(DafnyProblem... problems) {
        LOG.info("Validating problems...");
        //Check if the names of problems are all unique.
        Map<String, Long> counts = Arrays.stream(problems).map(DafnyProblem::name).collect(Collectors.groupingBy(Function.identity(), Collectors.counting()));
        counts.entrySet().stream().filter(a -> a.getValue() > 1).forEach(e -> {
            LOG.severe("The problem with name '" + e.getKey() + "' appears " + e.getValue() + " times in the file. Problem names must be unique.");
        });
        boolean valid = counts.size() == problems.length;
        if (valid) {
            for (DafnyProblem problem : problems) {
                if (problem.dafny() == null) {
                    LOG.severe("No dafny spec found for problem " + problem);
                    valid = false;
                } else {
                    if (problem.dafny().requires() == null) {
                        LOG.severe("No 'requires' array found in dafny spec for problem " + problem);
                        valid = false;
                    }
                    if (problem.dafny().ensures() == null) {
                        LOG.severe("No 'ensures' array found in dafny spec for problem " + problem);
                        valid = false;
                    }
                    if (problem.dafny().methodSignature() == null) {
                        LOG.severe("No method signature found in dafny spec for problem " + problem);
                        valid = false;
                    } else if (problem.dafny().methodSignature().isBlank())
                        LOG.warning("Blank method signature found in dafny spec for problem " + problem + " going to assume this is by design.");
                }
            }
        }
        return valid;
    }

    private static void processAllProblems(DafnyProblem... problems) {
        LOG.info("Processing " + problems.length + " problems.");
        boolean force = getConfig().containsKey(ConfigurationKeys.FORCE_RERUN_EXPERIMENTS);
        if (force)
            LOG.warning("The force flag is set. All previously completed experiments will now be re-run, and previous results will be overwritten.");
        for (DafnyProblem problem : problems) {
            LOG.info("Processing problem '" + problem.name() + "'");
            DafnyExperiment gen = new DafnyExperiment(PROBLEM_DATA_DIR, problem, manager);
            if (!force) {
                try {
                    if (gen.getStoredExperimentResult() != null) {
                        LOG.warning("Skipping experiment '" + problem.name() + "' as a result for it already exists. To ignore this check, re-run the program with the flag --force set.");
                        continue;
                    }
                } catch (IOException e) {
                    LOG.log(Level.SEVERE, "Failed to check if experiment " + problem.name() + " has previously been completed. Skipping experiment.", e);
                }
            }
            DafnyExperimentResult res = gen.execute();
            LOG.info("Experiment finished after " + res.resolutionAttempts() + " resolution and " + res.verificationAttempts() + " verification attempts, with result: " + res.outcome());
        }
    }


    public static Map<ConfigurationKeys, String> getConfig() {
        return config;
    }
}
