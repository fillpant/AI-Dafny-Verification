package click.nullpointer.genaidafny.dafny;

import click.nullpointer.genaidafny.openai.completion.OpenAICompletionManager;
import click.nullpointer.genaidafny.openai.completion.common.OpenAIMessage;
import click.nullpointer.genaidafny.openai.completion.common.OpenAIMessageRole;
import click.nullpointer.genaidafny.openai.completion.common.OpenAITextModel;
import click.nullpointer.genaidafny.openai.completion.requests.OpenAICompletionRequest;
import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonObject;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.concurrent.ExecutionException;
import java.util.stream.Collectors;

public class AIDafnyGenerator {
    private static final String PROMPT_STRUCTURE = "Write a Dafny program for the following task: \"%s\". The signature should be \"method %s\" and respect the following contract \"%s\".";
    private static final Gson GSON = new GsonBuilder().setPrettyPrinting().create();
    private final File cacheDir;
    private final DafnyProblem problem;
    private final OpenAICompletionManager completionManager;

    public AIDafnyGenerator(File cacheDir, DafnyProblem problem, OpenAICompletionManager completionManager) {
        this.cacheDir = cacheDir;
        if (!cacheDir.exists())
            cacheDir.mkdirs();
        this.problem = problem;
        this.completionManager = completionManager;
    }

    private String constructAIPrompt() {
        StringBuilder contract = new StringBuilder();
        contract.append(problem.dafny().requires().stream().map(a -> "requires " + a).collect(Collectors.joining(", ")));
        if (!problem.dafny().requires().isEmpty() && !problem.dafny().ensures().isEmpty())
            contract.append(", ");
        contract.append(problem.dafny().ensures().stream().map(a -> "ensures " + a).collect(Collectors.joining(", ")));
        return String.format(PROMPT_STRUCTURE, problem.statement(), problem.dafny().methodSignature(), contract.toString());
    }

    public String generateResponse() throws IOException, ExecutionException, InterruptedException {
        String cachedResponse = loadCachedResponse();
        if (cachedResponse != null)
            return cachedResponse;
        String prompt = constructAIPrompt();
        OpenAIMessage message = new OpenAIMessage(OpenAIMessageRole.USER, prompt);
        OpenAICompletionRequest req = new OpenAICompletionRequest(OpenAITextModel.GPT_4O_MINI, message);
        String resp = completionManager.submitCompletion(req).thenApply(a -> a.choices().getFirst().message().getContent()).get();
        cacheResponse(resp, prompt);
        return resp;
    }

    private void cacheResponse(String resp, String prompt) throws IOException {
        JsonObject obj = new JsonObject();
        obj.addProperty("response", resp);
        obj.addProperty("prompt", prompt);
        File cache = new File(cacheDir, problem.name() + ".json");
        Files.writeString(cache.toPath(), GSON.toJson(obj));
    }

    private String loadCachedResponse() throws IOException {
        File cache = new File(cacheDir, problem.name() + ".json");
        if (cache.exists() && cache.length() != 0) {
            String contents = Files.readString(cache.toPath());
            JsonObject data = GSON.fromJson(contents, JsonObject.class);
            return data.get("response").getAsString();
        }
        return null;
    }

}

