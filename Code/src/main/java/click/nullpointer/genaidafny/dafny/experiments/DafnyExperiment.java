package click.nullpointer.genaidafny.dafny.experiments;

import click.nullpointer.genaidafny.common.utils.Utilities;
import click.nullpointer.genaidafny.dafny.CLIProgramOutput;
import click.nullpointer.genaidafny.dafny.DafnyCLIIntegrator;
import click.nullpointer.genaidafny.dafny.DafnyProblem;
import click.nullpointer.genaidafny.openai.completion.OpenAICompletionManager;
import click.nullpointer.genaidafny.openai.completion.common.OpenAIMessage;
import click.nullpointer.genaidafny.openai.completion.common.OpenAIMessageRole;
import click.nullpointer.genaidafny.openai.completion.common.OpenAITextModel;
import click.nullpointer.genaidafny.openai.completion.requests.OpenAICompletionRequest;
import click.nullpointer.genaidafny.openai.completion.requests.formats.OpenAIStructuredResponseFormat;
import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Files;
import java.util.ArrayList;
import java.util.List;
import java.util.Objects;
import java.util.concurrent.ExecutionException;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Collectors;

public class DafnyExperiment {
    private static final int MAX_GEN_AI_INTERACTIONS = 10;
    private static final String INITIAL_PROMPT_STRUCTURE = "You are given the following task to perform in Dafny: \"%s\". The signature should be: \"%s\". The method should respect the following contract: \"%s\". Produce and show only the Dafny body of this method, including the curly braces that surround it. Do not show the signature nor contract.";
    private static final String RESOLVE_FAIL_PROMPT_STRUCTURE = "Consider the below dafny method: \n%s\n When using dafny resolve, the below error is emitted and resolve fails: \n%s\nCorrect the error by altering only the method body. Produce and show only the Dafny body, including the curly braces that surround it. Do not show the signature nor contract.";
    private static final String VERIFY_FAIL_PROMPT_STRUCTURE = "Consider the below dafny method: \n%s\n When using dafny verify, the below error is emitted and verify fails: \n%s\nCorrect the error by altering only the method body. Produce and show only the Dafny body, including the curly braces that surround it. Do not show the signature nor contract.";
    private static final Gson GSON = new GsonBuilder().setPrettyPrinting().create();
    private static final JsonObject STRUCTURED_RESPONSE_JSON = GSON.fromJson("""
            {
              "name": "d",
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
    private final Logger log;
    private final File problemDir;
    private final DafnyProblem problem;
    private final OpenAICompletionManager completionManager;
    private final DafnyExperimentCache cache;
    private final List<OpenAIMessage> genAIMessages = new ArrayList<>();
    private volatile DafnyExperimentState currentState = DafnyExperimentState.NOT_STARTED;
    private int resolutionAttempts = 0;
    private int verificationAttempts = 0;
    private int genAIInteractions = 0;

    public DafnyExperiment(File rootDir, DafnyProblem problem, OpenAICompletionManager completionManager) {
        Objects.requireNonNull(rootDir);
        Objects.requireNonNull(problem);
        Objects.requireNonNull(completionManager);
        this.problemDir = new File(rootDir, problem.getFileSafeName());
        this.problemDir.mkdirs();
        this.log = Utilities.createLogger("Experiment '" + problem.name() + "'", new File(this.problemDir, "program_logs.log"));
        this.problem = problem;
        this.completionManager = completionManager;
        this.cache = new DafnyExperimentCache(new File(problemDir, "caches.json"));
        log.info("Experiment created.");
    }

    public DafnyExperimentResult execute() {
        if (currentState != DafnyExperimentState.NOT_STARTED)
            throw new IllegalStateException("Experiment is no longer runnable.");

        currentState = DafnyExperimentState.RUNNING;
        DafnyExperimentOutcome outcome = DafnyExperimentOutcome.SUCCESS;
        log.info("Experiment started.");
        try {
            String prompt = constructAIPrompt();
            log.info("Using initial prompt: " + prompt);

            while (genAIInteractions < MAX_GEN_AI_INTERACTIONS) {
                log.info("Querrying GenAI...");
                genAIInteractions++;
                String aiMethodBody = generateResponse(prompt);


                log.info("Converting GenAI response to method...");
                String method = turnGenAIResponseToDafnyMethod(aiMethodBody);
                saveExperimentFile("program.dfy", method);//This is fine, we overwrite each time.

                log.info("Calling dafny to resolve the generated method...");
                //resolve. On fail, retry up to count, keep results in json array styore in resolve_result.json
                CLIProgramOutput resolveOut = DafnyCLIIntegrator.resolve(new File(problemDir, "program.dfy"));
                logCLIResult(resolveOut);
                resolutionAttempts++;
                if (resolveOut.exitCode() != 0) {
                    log.warning("Failed to resolve the generated method. Preparing GenAI prompt to fix...");
                    prompt = constructResolutionPrompt(resolveOut.getFullScreenOutput(), method);
                    continue; //oops
                }

                log.info("Dafny resolution check passed.");

                log.info("Calling dafny to verify the generated method...");
                CLIProgramOutput verifyOut = DafnyCLIIntegrator.verify(new File(problemDir, "program.dfy"));
                logCLIResult(resolveOut);
                verificationAttempts++;
                if (verifyOut.exitCode() != 0) {
                    log.warning("Failed to verify the generated method. Preparing GenAI prompt to fix...");
                    prompt = constructVerificationPrompt(verifyOut.getFullScreenOutput(), method);
                    continue;
                }
                log.info("Dafny verification check passed.");
                break; //Poor code restructure.
            }
            if (MAX_GEN_AI_INTERACTIONS >= genAIInteractions) {
                log.warning("Experiment stopped due to too many GenAI interactions.");
            } else {
                log.info("Experiment finished.");
            }
        } catch (Exception e) {
            log.log(Level.SEVERE, "Experiment terminated exceptionally", e);
            outcome = DafnyExperimentOutcome.FAILURE_INTERNAL_ERROR;
        } finally {
            currentState = DafnyExperimentState.FINISHED;
            scilentGenAIMessageSave();
        }
        //Infer outcome if not set to failure_internal_error.
        if (outcome == DafnyExperimentOutcome.SUCCESS) {
            if (genAIInteractions >= MAX_GEN_AI_INTERACTIONS) {
                outcome = verificationAttempts == 0 ? DafnyExperimentOutcome.FAILURE_RESOLVE : DafnyExperimentOutcome.FAILURE_VERIFY;
            }
        }
        DafnyExperimentResult result = new DafnyExperimentResult(outcome, verificationAttempts, resolutionAttempts);
        try {
            saveExperimentFile("experiment_result.json", GSON.toJson(result));
        } catch (IOException e) {
            log.log(Level.SEVERE, "Failed to save experiment result!", e);
        }
        return result;
    }

    /**
     * Returns the last {@link DafnyExperimentResult} that was stored to file.
     * This method may only be called before this experiment is started, or after it has finished.
     *
     * @return The last stored result, or null if one is not available.
     * @throws IOException if an IO error arises while retrieving the last stored result.
     */
    public DafnyExperimentResult getStoredExperimentResult() throws IOException {
        File resultFile = new File(problemDir, "experiment_result.json");
        if (!resultFile.exists() || resultFile.length() == 0)
            return null;
        try (FileReader reader = new FileReader(resultFile)) {
            return GSON.fromJson(reader, DafnyExperimentResult.class);
        }
    }

    private String constructVerificationPrompt(String fullScreenOutput, String fullMethod) {
        return VERIFY_FAIL_PROMPT_STRUCTURE.formatted(fullMethod, fullScreenOutput);
    }

    private String constructResolutionPrompt(String fullScreenOutput, String fullMethod) throws ExecutionException, InterruptedException {
        return RESOLVE_FAIL_PROMPT_STRUCTURE.formatted(fullMethod, fullScreenOutput);
    }

    private void logCLIResult(CLIProgramOutput resolveOut) {
        Level level = resolveOut.exitCode() == 0 ? Level.INFO : Level.SEVERE;
        log.log(level, "Program exited with code " + resolveOut.exitCode());
        if (!resolveOut.stderr().isBlank())
            log.log(level, "Program stderr: " + resolveOut.stderr());
        if (!resolveOut.stdout().isBlank())
            log.log(level, "Program stdout: " + resolveOut.stdout());
    }

    private void scilentGenAIMessageSave() {
        try {
            saveExperimentFile("gen_ai_messages.json", GSON.toJson(genAIMessages));
            JsonArray arr = new JsonArray();
            for (OpenAIMessage message : genAIMessages) {
                JsonObject obj = new JsonObject();
                obj.addProperty("role", message.getRole().toString());
                obj.addProperty("content", message.getContent());
                arr.add(obj);
            }
            saveExperimentFile("gen_ai_messages_simple.json", GSON.toJson(arr));
        } catch (IOException e) {
            log.log(Level.WARNING, "Failed to save Gen AI message log in scilent call. Skipping.", e);
        }
    }

    private void saveExperimentFile(String name, String content) throws IOException {
        log.fine("Saving " + name);
        File out = new File(problemDir, name);
        Files.writeString(out.toPath(), content);
        log.fine("Saved " + content.length() + " characters to file " + name);
    }

    private String constructAIPrompt() {
        StringBuilder contract = new StringBuilder();
        contract.append(problem.dafny().requires().stream().map(a -> "requires " + a).collect(Collectors.joining(", ")));
        if (!problem.dafny().requires().isEmpty() && !problem.dafny().ensures().isEmpty())
            contract.append(", ");
        contract.append(problem.dafny().ensures().stream().map(a -> "ensures " + a).collect(Collectors.joining(", ")));
        return String.format(INITIAL_PROMPT_STRUCTURE, problem.statement(), "method " + problem.dafny().methodSignature(), contract.toString());
    }

    private String generateResponse(String prompt) throws ExecutionException, InterruptedException {
        String resp = cache.getCachedResponse(prompt);
        if (resp != null) {
            log.fine("Cache hit, not querying GenAI");
            return resp;
        }
        log.fine("Constructing message for GenAI");
        OpenAIMessage message = new OpenAIMessage(OpenAIMessageRole.USER, prompt);
        genAIMessages.add(message);
        OpenAICompletionRequest req = new OpenAICompletionRequest(OpenAITextModel.GPT_4O_MINI, message);
        req.setResponseFormat(new OpenAIStructuredResponseFormat(STRUCTURED_RESPONSE_JSON));
        log.fine("Using model " + req.getModel() + ". Awaiting response...");
        OpenAIMessage responseMsg = completionManager.submitCompletion(req)
                .thenApply(a -> a.choices().getFirst().message())
                .get();
        genAIMessages.add(responseMsg);
        resp = responseMsg.getContent();
        log.fine("Got response with " + resp.length() + " characters.");
        JsonObject parsedResp = GSON.fromJson(resp, JsonObject.class);
        resp = parsedResp.get("method_body").getAsString();
        cache.cacheResponse(prompt, resp);
        scilentGenAIMessageSave();
        return resp;
    }

    private String turnGenAIResponseToDafnyMethod(String response) {
        StringBuilder sb = new StringBuilder();
        sb.append("method ").append(problem.dafny().methodSignature()).append("\n");
        problem.dafny().requires().forEach(a -> sb.append("\t").append("requires ").append(a).append("\n"));
        problem.dafny().ensures().forEach(a -> sb.append("\t").append("ensures ").append(a).append("\n"));
        sb.append(response);
        return sb.toString();
    }
}

