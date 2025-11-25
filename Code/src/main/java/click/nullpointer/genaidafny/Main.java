package click.nullpointer.genaidafny;

import click.nullpointer.genaidafny.dafny.AIDafnyGenerator;
import click.nullpointer.genaidafny.dafny.DafnyProblem;
import click.nullpointer.genaidafny.openai.completion.OpenAICompletionManager;
import com.google.gson.Gson;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.util.Arrays;
import java.util.Map;
import java.util.concurrent.ExecutionException;
import java.util.function.Function;
import java.util.stream.Collectors;

public class Main {
    private static final File LOG_DIR = new File("openai_promp_logs");
    private static final File PROBLEM_RESPONSE_CACHE = new File("openai_problem_response_cache");
    private static final File PROBLEM_FILE = new File("resources/problems.json");
    private static final Gson GSON = new Gson();
    private static OpenAICompletionManager manager;


    public static void main(String... args) throws IOException, ExecutionException, InterruptedException {
        manager = new OpenAICompletionManager(System.getenv().get("OPENAI_KEY"), LOG_DIR);
        try (FileReader fr = new FileReader(PROBLEM_FILE)) {
            DafnyProblem[] problems = GSON.fromJson(fr, DafnyProblem[].class);
            validateProblemList(problems);
            processAllProblems(problems[4]);
        }
    }

    private static void validateProblemList(DafnyProblem... problems) {
        //Check if the names of problems are all unique.
        Map<String, Long> counts = Arrays.stream(problems).map(DafnyProblem::name).collect(Collectors.groupingBy(Function.identity(), Collectors.counting()));
        counts.entrySet().stream().filter(a -> a.getValue() > 1).forEach(e -> {
            System.err.println("The problem with name '" + e.getKey() + "' appears " + e.getValue() + " times in the file. Problem names must be unique.");
        });
        if (counts.size() != problems.length) {
            throw new IllegalStateException("The input file is invalid.");
        }
    }

    private static void processAllProblems(DafnyProblem... problems) throws IOException, ExecutionException, InterruptedException {
        for (DafnyProblem problem : problems) {
            AIDafnyGenerator gen = new AIDafnyGenerator(PROBLEM_RESPONSE_CACHE, problem, manager);
            String response = gen.generateResponse();
            System.out.println(response);//TODO
        }
    }
}
