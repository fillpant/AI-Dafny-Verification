package click.nullpointer.genaidafny.dafny;

import click.nullpointer.genaidafny.openai.completion.OpenAICompletionManager;
import click.nullpointer.genaidafny.openai.completion.common.OpenAIMessage;
import click.nullpointer.genaidafny.openai.completion.common.OpenAIMessageRole;
import click.nullpointer.genaidafny.openai.completion.common.OpenAITextModel;
import click.nullpointer.genaidafny.openai.completion.requests.OpenAICompletionRequest;
import click.nullpointer.genaidafny.openai.completion.requests.formats.OpenAIStructuredResponseFormat;
import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonObject;

import java.io.File;
import java.io.IOException;
import java.nio.file.Files;
import java.util.concurrent.ExecutionException;
import java.util.stream.Collectors;

public class AIDafnyGenerator {
    private static final String PROMPT_STRUCTURE = "You are given the following task to perform in Dafny: \"%s\". The signature should be: \"%s\". The method should respect the following contract: \"method %s\". Produce and show only the Dafny body of this method, including the curly braces that surround it. Do not show the signature nor contract.";
    private static final Gson GSON = new GsonBuilder().setPrettyPrinting().create();
    private static final JsonObject STRUCTURED_RESPONSE_JSON = GSON.fromJson("""
            {
              "name": "dr",
              "strict": true,
              "schema": {
                "type": "object",
                "properties": {
                  "method_body": {
                    "type": "string"
                  }
                },
                "additionalProperties": false,
                "required": [
                  "method_body"
                ]
              }
            }
            """, JsonObject.class);
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
        String resp = loadCachedResponse();
        if (resp == null) {
            String prompt = constructAIPrompt();
            OpenAIMessage message = new OpenAIMessage(OpenAIMessageRole.USER, prompt);
            OpenAICompletionRequest req = new OpenAICompletionRequest(OpenAITextModel.GPT_4O_MINI, message);
            req.setResponseFormat(new OpenAIStructuredResponseFormat(STRUCTURED_RESPONSE_JSON));
            resp = completionManager.submitCompletion(req).thenApply(a -> a.choices().getFirst().message().getContent()).get();
            cacheResponse(resp, prompt);
        }
        JsonObject parsedResp = GSON.fromJson(resp, JsonObject.class);
        return turnGenAIResponseToDafnyMethod(parsedResp.get("method_body").getAsString());
    }

    private String turnGenAIResponseToDafnyMethod(String response) {
        StringBuilder sb = new StringBuilder();
        sb.append("method ").append(problem.dafny().methodSignature()).append("\n");
        problem.dafny().requires().forEach(a -> sb.append("\t").append("requires ").append(a).append("\n"));
        problem.dafny().ensures().forEach(a -> sb.append("\t").append("ensures ").append(a).append("\n"));
        sb.append(response);
        return sb.toString();
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

