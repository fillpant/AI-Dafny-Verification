package click.nullpointer.genaidafny.dafny.experiments;

import click.nullpointer.genaidafny.Main;
import click.nullpointer.genaidafny.common.utils.EventTimer;
import click.nullpointer.genaidafny.common.utils.Utilities;
import click.nullpointer.genaidafny.config.ConfigurationKeys;
import click.nullpointer.genaidafny.dafny.CLIProgramOutput;
import click.nullpointer.genaidafny.dafny.DafnyCLIIntegrator;
import click.nullpointer.genaidafny.dafny.DafnyProblem;
import click.nullpointer.genaidafny.dafny.experiments.cache.DafnyExperimentCache;
import click.nullpointer.genaidafny.dafny.experiments.cache.DummyDafnyExperimentCache;
import click.nullpointer.genaidafny.dafny.experiments.cache.IExperimentCache;
import click.nullpointer.genaidafny.openai.completion.OpenAICompletionManager;
import click.nullpointer.genaidafny.openai.completion.common.OpenAIMessage;
import click.nullpointer.genaidafny.openai.completion.common.OpenAIMessageRole;
import click.nullpointer.genaidafny.openai.completion.common.OpenAITextModel;
import click.nullpointer.genaidafny.openai.completion.requests.OpenAICompletionRequest;
import click.nullpointer.genaidafny.openai.completion.requests.OpenAIReasoningModelEffort;
import click.nullpointer.genaidafny.openai.completion.requests.formats.OpenAIStructuredResponseFormat;
import click.nullpointer.genaidafny.openai.completion.responses.OpenAICompletionResponse;
import com.google.gson.Gson;
import com.google.gson.GsonBuilder;
import com.google.gson.JsonArray;
import com.google.gson.JsonObject;

import java.io.File;
import java.io.FileReader;
import java.io.IOException;
import java.nio.file.Files;
import java.nio.file.StandardCopyOption;
import java.util.ArrayList;
import java.util.List;
import java.util.Map;
import java.util.Objects;
import java.util.concurrent.ExecutionException;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Collectors;

public class DafnyExperiment {

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
    private final IExperimentCache cache;
    private final List<TransactionUnion> genAIMessages = new ArrayList<>();
    private final int maxTokensForExperiment;
    private volatile DafnyExperimentState currentState = DafnyExperimentState.NOT_STARTED;
    private int hardFailedResolutions = 0; //fail because of error
    private int softFailedResolutions = 0; //fail because of warning
    private int resolutionAttempts = 0; //Total resolution attempts.
    private int badResponses = 0; //Number of times GenAI returned no response (likely due to being caught in an infinite loop)
    private int verificationAttempts = 0;
    private int methodsWithAssumeClauses = 0;
    private int genAIInteractions = 0;
    private int totalTokens = 0;
    private EventTimer timer = new EventTimer();

    public DafnyExperiment(File rootDir, DafnyProblem problem, OpenAICompletionManager completionManager) {
        Objects.requireNonNull(rootDir);
        Objects.requireNonNull(problem);
        Objects.requireNonNull(completionManager);
        this.maxTokensForExperiment = Integer.parseInt(Main.getConfig().get(ConfigurationKeys.MAX_TOTAL_TOKENS_PER_EXPERIMENT));
        this.problemDir = new File(rootDir, problem.getFileSafeName());
        this.problemDir.mkdirs();
        this.log = Utilities.createLogger("Experiment '" + problem.name() + "'", new File(this.problemDir, "program_logs.log"));
        this.problem = problem;
        this.completionManager = completionManager;
        if (!Main.getConfig().containsKey(ConfigurationKeys.DISABLE_EXPERIMENT_CACHE))
            this.cache = new DafnyExperimentCache(new File(problemDir, "caches.json"));
        else
            this.cache = new DummyDafnyExperimentCache();
        log.info("Experiment created.");
    }

    public DafnyExperimentResult execute() {
        if (currentState != DafnyExperimentState.NOT_STARTED)
            throw new IllegalStateException("Experiment is no longer runnable.");
        timer.startEvent("Overall Experiment");
        currentState = DafnyExperimentState.RUNNING;
        DafnyExperimentOutcome outcome = DafnyExperimentOutcome.SUCCESS;
        log.info("Experiment started.");
        final int maxGenAIInteractions = Integer.parseInt(Main.getConfig().get(ConfigurationKeys.MAX_GEN_AI_INTERACTIONS));
        try {
            int iteration = 0;
            String prompt = constructAIPrompt();
            log.info("Using initial prompt: " + prompt);
            while (genAIInteractions < maxGenAIInteractions && totalTokens < maxTokensForExperiment) {
                log.info("There are " + (maxTokensForExperiment - totalTokens) + " left in the jar, for the rest of this experiment.");
                EventTimer.EventTimingRecord lastEvent = timer.getLastStoppedEvent();
                if (lastEvent != null)
                    log.info("Previous iteration lasted " + lastEvent.getDurationMs() + "ms");
                iteration++;
                timer.startEvent("Iteration #" + iteration);
                log.info("Querrying GenAI...");
                genAIInteractions++;
                String aiMethodBody = generateResponse(prompt);
                if (aiMethodBody == null) {
                    log.severe("Failed to aquire code from GenAI. Will re-try up to limit.");
                    badResponses++;
                    timer.stopEvent("Iteration #" + iteration);
                    continue;
                }

                log.info("Converting GenAI response to a program...");
                String method = turnGenAIResponseToDafnyProgram(aiMethodBody);
                saveExperimentFile("program.dfy", method);//This is fine, we overwrite each time.

                //If the amount of messages to send in the context does contain the very first request, then we deem context to be
                // 'enabled' for the purposes
                //of prompt selection.
                //If the context window has excluded the first prompt (request), then we must switch to the second line of defense,
                // whereby the request
                // contains the full method previously provided.
                boolean contextEnabled =
                        Integer.parseInt(Main.getConfig().get(ConfigurationKeys.MAX_CONTEXT_MESSAGES_COUNT)) >= genAIMessages.size();
                if (contextEnabled) {
                    log.info("Context is treated as being fully enabled, meaning that subsequent prompts do not include the full code.");
                } else {
                    log.info("Context is limited beyond the amount of previous messages, or is disabled entirely. Treating any subsequent" +
                            " GenAI requests as needing the full method body in them.");
                }
                log.info("Checking the code for the presence of the 'assume' keyword...");
                //If, without comments and string literals the word assume appears, then it is reasonable to expect it's used as a keyword.
                if (Utilities.lightStripCommentsAndStringsFromDafny(method).toLowerCase().contains("assume")) {
                    log.warning("GenAI has produced code with one or more 'assume' keywords. Rejecting, and re-prompting to fix...");
                    methodsWithAssumeClauses++;
                    //prompt = constructAssumePrompt(problem.dafny().methodSignature(), problem.statement(), method, contextEnabled);
                    prompt = getPrompt(contextEnabled ? PromptSelection.CONTEXT_ON_ASSUME_USED_FAIL : PromptSelection.ASSUME_USED_FAIL,
                            method, null);
                    timer.stopEvent("Iteration #" + iteration);
                    continue;
                }

                log.info("Calling dafny to resolve the generated code...");
                //resolve. On fail, retry up to count, keep results in json array styore in resolve_result.json
                CLIProgramOutput resolveOut = DafnyCLIIntegrator.resolve(new File(problemDir, "program.dfy"));
                logCLIResult(resolveOut);
                resolutionAttempts++;

                log.info("Calling dafny to resolve the generated code, but with warnings allowed...");
                CLIProgramOutput resolveOutWithWarningsAllowd = DafnyCLIIntegrator.resolve(new File(problemDir, "program.dfy"), "--allow" +
                        "-warnings");
                logCLIResult(resolveOutWithWarningsAllowd);
                if (resolveOutWithWarningsAllowd.exitCode() == 0) {
                    if (resolveOut.exitCode() != 0) {
                        softFailedResolutions++;
                        log.info("Resolution fails as a result of a warning, but passes with warnings disabled.");
                    }
                    if (resolveOut.exitCode() == 0)
                        log.info("Resolution passes without warnings.");
                } else {
                    hardFailedResolutions++;
                    log.info("Resolution fails as a result of an error.");
                }
                if (resolveOut.exitCode() != 0) {
                    //If resolution fails with warnings, it will also fail without, hence this is the place for this check.
                    if (outcome == DafnyExperimentOutcome.SUCCESS)
                        outcome = DafnyExperimentOutcome.FAILURE_RESOLVE;
                    log.warning("Treating resolution as failed for the generated code. Preparing GenAI prompt to fix...");
                    //prompt = constructResolutionPrompt(problem.dafny().methodSignature(), problem.statement(), resolveOut
                    // .getFullScreenOutput(), method, contextEnabled);
                    prompt = getPrompt(contextEnabled ? PromptSelection.CONTEXT_ON_RESOLVE_FAIL : PromptSelection.RESOLVE_FAIL, method,
                            resolveOut.getFullScreenOutput());
                    timer.stopEvent("Iteration #" + iteration);
                    continue; //oops
                }

                log.info("Dafny resolution check passed.");
                log.info("Calling dafny to verify the generated code...");
                CLIProgramOutput verifyOut = DafnyCLIIntegrator.verify(new File(problemDir, "program.dfy"));
                logCLIResult(verifyOut);
                verificationAttempts++;
                if (verifyOut.exitCode() != 0) {
                    //If the verification failed, indescriminatly set outcome
                    outcome = DafnyExperimentOutcome.FAILURE_VERIFY;
                    log.warning("Failed to verify the generated code. Preparing GenAI prompt to fix...");
                    //prompt = constructVerificationPrompt(problem.dafny().methodSignature(), problem.statement(), verifyOut
                    // .getFullScreenOutput(), method, contextEnabled);
                    prompt = getPrompt(contextEnabled ? PromptSelection.CONTEXT_ON_VERIFY_FAIL : PromptSelection.VERIFY_FAIL, method,
                            verifyOut.getFullScreenOutput());

                    timer.stopEvent("Iteration #" + iteration);
                    continue;
                } else {
                    //If A verification passes, then success overall.
                    outcome = DafnyExperimentOutcome.SUCCESS;
                }
                log.info("Dafny verification check passed.");
                timer.stopEvent("Iteration #" + iteration);
                break; //Poor code restructure.
            }
            if (maxGenAIInteractions <= genAIInteractions) {
                log.warning("Experiment stopped due to too many GenAI interactions.");
            } else if (Integer.parseInt(Main.getConfig().get(ConfigurationKeys.MAX_TOTAL_TOKENS_PER_EXPERIMENT)) <= totalTokens) {
                log.warning("Experiment stopped after using " + totalTokens + " tokens, which exceeds the limit specified. ");
            } else {
                log.info("Experiment finished.");
            }
        } catch (Exception e) {
            log.log(Level.SEVERE, "Experiment terminated exceptionally", e);
            outcome = DafnyExperimentOutcome.FAILURE_INTERNAL_ERROR;
        } finally {
            timer.stopEvent("Overall Experiment");
            currentState = DafnyExperimentState.FINISHED;
            scilentGenAIMessageSave();
        }
        DafnyExperimentResult result = new DafnyExperimentResult(outcome, getUsageStats(), badResponses, verificationAttempts,
                resolutionAttempts, softFailedResolutions, hardFailedResolutions, methodsWithAssumeClauses, timer);
        try {
            saveExperimentFile("experiment_result.json", GSON.toJson(result));
        } catch (IOException e) {
            log.log(Level.SEVERE, "Failed to save experiment result!", e);
        }
        if (!Main.getConfig().containsKey(ConfigurationKeys.DISABLE_LATEX_REPORT)) {
            String tex = experimentInfoToTex(result);
            try {
                saveAndCompileLaTeX(tex);
            } catch (IOException | InterruptedException e) {
                log.log(Level.SEVERE, "Failed to save and compile pdf report!", e);
            }
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

    /**
     * Get the usage statistics of the current experiment. This method will collate the data at the time it is being called.
     * It is not recommended this method is called while the experiment is running, as its not threadsafe.
     * Calling this method on a new experiment, will return 0.
     *
     * @return a {@link DafnyExperimentTokenUsage} instance with the usage values.
     */
    public DafnyExperimentTokenUsage getUsageStats() {
        int tokensInput =
                genAIMessages.stream().filter(a -> a.openAIResponseDetails() != null).mapToInt(a -> a.openAIResponseDetails().usage().promptTokens()).sum();
        int tokensOutput =
                genAIMessages.stream().filter(a -> a.openAIResponseDetails() != null).mapToInt(a -> a.openAIResponseDetails().usage().completionTokens()).sum();
        int totalSum =
                genAIMessages.stream().filter(a -> a.openAIResponseDetails() != null).mapToInt(a -> a.openAIResponseDetails().usage().totalTokens()).sum();
        int totalReasoning =
                genAIMessages.stream().filter(a -> a.openAIResponseDetails() != null).mapToInt(a -> a.openAIResponseDetails().usage().completionTokensDetails().reasoningTokens()).sum();
        return new DafnyExperimentTokenUsage(tokensInput, tokensOutput, totalSum, totalReasoning);
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
            for (TransactionUnion resp : genAIMessages) {
                OpenAIMessage message = resp.message();
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

    private String getContractForPrompt() {
        StringBuilder contract = new StringBuilder();
        contract.append(problem.dafny().requires().stream().map(a -> "requires " + a).collect(Collectors.joining(", ")));
        if (!problem.dafny().requires().isEmpty() && !problem.dafny().ensures().isEmpty())
            contract.append(", ");
        contract.append(problem.dafny().ensures().stream().map(a -> "ensures " + a).collect(Collectors.joining(", ")));
        return contract.toString();
    }

    private String constructAIPrompt() {
        return getPrompt(PromptSelection.INITIAL_PROMPT, null, null);
    }

    private String generateResponse(String prompt) throws ExecutionException, InterruptedException {
        String resp = cache.getCachedResponse(prompt);
        if (resp != null) {
            log.fine("Cache hit, not querying GenAI");
            return resp;
        }
        log.fine("Constructing message for GenAI");
        OpenAIMessage message = new OpenAIMessage(OpenAIMessageRole.USER, prompt);
        genAIMessages.add(new TransactionUnion(message, null));


        List<OpenAIMessage> context = new ArrayList<>();
        int ctxtSize = Integer.parseInt(Main.getConfig().get(ConfigurationKeys.MAX_CONTEXT_MESSAGES_COUNT));
        if (ctxtSize > 0) {
            context.addAll(genAIMessages.stream().limit(ctxtSize).map(TransactionUnion::message).toList());
            log.info("Context is on, attaching " + context.size() + " previous messages in the request to GenAI.");
        }
        context.add(message);
        OpenAITextModel model = OpenAITextModel.valueOf(Main.getConfig().get(ConfigurationKeys.GEN_AI_MODEL));
        OpenAIReasoningModelEffort effort = Main.getConfig().get(ConfigurationKeys.GEN_AI_REASONING_EFFORT) == null ? null :
                OpenAIReasoningModelEffort.valueOf(Main.getConfig().get(ConfigurationKeys.GEN_AI_REASONING_EFFORT));
        OpenAICompletionRequest req = new OpenAICompletionRequest(model, context.toArray(new OpenAIMessage[0]));
        req.setResponseFormat(new OpenAIStructuredResponseFormat(STRUCTURED_RESPONSE_JSON));
        if (effort != null) {
            if (model.isReasoning()) {
                req.setReasoningEffort(effort);
            } else {
                log.warning("Ignoring configured reasoning effort. Model chosen (" + model + ") is not a reasoning model.");
            }
        } else {
            if (model.isReasoning()) {
                req.setReasoningEffort(OpenAIReasoningModelEffort.MEDIUM);
                log.info("A reasoning model is chosen, but no reasoning effort value is set. Setting reasoning to 'medium'");
            }
        }
        //Take max tokens per request and max tokens for experiment
        //Pick whatever's smallest.
        int maxTokens = Math.min(Integer.parseInt(Main.getConfig().get(ConfigurationKeys.MAX_GEN_AI_OUTPUT_TOKENS)),
                maxTokensForExperiment);
        //If the tokens alloted to this experiment are fewer than the max tokens per request, use those.
        maxTokens = Math.min(maxTokensForExperiment - totalTokens, maxTokens);//How many left in the jar, versus
        if (maxTokens > 0) {
            log.fine("Setting max tokens for the request to " + maxTokens);
            req.setMaxCompletionTokens(maxTokens);
        }
        log.fine("Using model " + req.getModel() + ". Awaiting response...");
        OpenAICompletionResponse oaiResp = completionManager.submitCompletion(req).get();
        totalTokens += oaiResp.usage().totalTokens();
        OpenAIMessage responseMsg = oaiResp.choices().getFirst().message();
        genAIMessages.add(new TransactionUnion(responseMsg, oaiResp));
        if (!oaiResp.choices().getFirst().finishReason().equalsIgnoreCase("stop")) {
            String stop = oaiResp.choices().getFirst().finishReason();
            log.severe("Model finished with non 'stop' reason: " + stop + ".");
            scilentGenAIMessageSave();
            return null;
        }

        resp = responseMsg.getContent();
        log.fine("Got response with " + resp.length() + " characters.");
        JsonObject parsedResp = GSON.fromJson(resp, JsonObject.class);
        resp = parsedResp.get("method_body").getAsString();
        cache.cacheResponse(prompt, resp);
        scilentGenAIMessageSave();
        return resp;
    }


    private String getPrompt(PromptSelection selection, String generatedMethod, String errorMessage) {
        StringBuilder prompt = new StringBuilder();
        String methodSig = problem.dafny().methodSignature();
        if (methodSig == null || methodSig.isBlank())
            methodSig = "";
        String contract =
                ((problem.dafny().ensures() != null && !problem.dafny().ensures().isEmpty()) || (problem.dafny().requires() != null && !problem.dafny().requires().isEmpty())) ? getContractForPrompt() : "";
        String functionalCode = problem.dafny().functionalCode();
        if (functionalCode == null || functionalCode.isBlank())
            functionalCode = "";
        if (!contract.isEmpty() && methodSig.isEmpty()) {
            throw new IllegalArgumentException("Cannot expect a contract to be met when no method signature is provided.");
        }
        if ((methodSig.isEmpty() || contract.isEmpty()) && !functionalCode.isEmpty()) {
            throw new IllegalArgumentException("Cannot have functional code when a method and contract is absent!");
        }

        String codeOrMethod = methodSig.isEmpty() ? "code" : "method";

        switch (selection) {
            case INITIAL_PROMPT:
                prompt.append("You are given the following task to perform in Dafny:\n\n");
                if (problem.statement() != null && !problem.statement().isBlank())
                    prompt.append(problem.statement());
                else
                    prompt.append("Write a method to satisfy the below requirements.");
                prompt.append("\n\n");

                if (!methodSig.isEmpty())
                    prompt.append("The signature should be:\n\n").append(methodSig).append("\n\n");
                if (!contract.isEmpty())
                    prompt.append("The method should respect the following contract:\n\n").append(contract).append("\n\n");
                if (!functionalCode.isEmpty())
                    prompt.append("The contract uses the following dafny code:\n\n").append(functionalCode).append("\n\nThese " +
                            "function(s) must not be used in your implementation of the method.\n\n");
                if (!methodSig.isEmpty())
                    prompt.append("Produce and show only the Dafny body of this method, including the curly braces that surround it. Do " +
                            "not " +
                            "show the signature nor contract. You must not use 'assume' anywhere in your code.");
                else
                    prompt.append("Produce and show code in Dafny to address this task. You must not use 'assume' anywhere in your code.");
                break;
            case RESOLVE_FAIL:
            case VERIFY_FAIL:
                if (errorMessage == null || errorMessage.isBlank())
                    throw new IllegalArgumentException("RESOLVE_FAIL/VERIFY_FAIL requires errorMessage");
            case ASSUME_USED_FAIL:
                if (generatedMethod == null || generatedMethod.isBlank())
                    throw new IllegalArgumentException("RESOLVE_FAIL/VERIFY_FAIL/ASSUME_USED_FAIL requires generatedMethod");
                prompt.append("Consider the ").append(codeOrMethod).append(" ").append(methodSig.isEmpty() ? "" : methodSig + " ").append("shown below:\n\n");
                prompt.append(generatedMethod).append("\n\n");
                prompt.append("This ").append(codeOrMethod).append(" was generated to satisfy the following task:\n\n");
                if (problem.statement() != null && !problem.statement().isBlank())
                    prompt.append(problem.statement());
                else
                    prompt.append("Write a method to satisfy the below requirements.");
                prompt.append("\n\n");
                if (!contract.isEmpty())
                    prompt.append("The ").append(codeOrMethod).append(" should respect the following contract:\n\n").append(contract).append("\n\n");
                String actionWord = selection == PromptSelection.RESOLVE_FAIL ? "resolve" : "verify";
                if (selection == PromptSelection.ASSUME_USED_FAIL) {
                    prompt.append("The ").append(codeOrMethod).append(" makes use of 'assume'. Correct the ").append(codeOrMethod);
                    if (!methodSig.isEmpty())
                        prompt.append(" by altering only the method body, to not use 'assume'. Produce and show only the Dafny body, " +
                                "including the curly braces that surround it. Do not show the signature nor contract.");
                    else
                        prompt.append(" making any required change. You must not use 'assume' anywhere in your code.");
                    break;
                }
                prompt.append("When using dafny ").append(actionWord).append(", the below error is emitted and ").append(actionWord).append(" fails:\n\n");
                prompt.append(errorMessage).append("\n\n");
                if (!methodSig.isEmpty())
                    prompt.append("Correct the error by altering only the method body. Produce and show only the Dafny body, including " +
                            "the curly braces that surround it. Do not show the signature nor contract. You must not use 'assume' " +
                            "anywhere in your code.");
                else
                    prompt.append("Correct the error by altering the given code. Produce and show the full fixed code. You must not use " +
                            "'assume' anywhere in your code.");
                break;

            case CONTEXT_ON_RESOLVE_FAIL:
            case CONTEXT_ON_VERIFY_FAIL:
                if (errorMessage == null || errorMessage.isBlank() || generatedMethod == null || generatedMethod.isBlank())
                    throw new IllegalArgumentException("CONTEXT_ON_VERIFY_FAIL/CONTEXT_ON_RESOLVE_FAIL requires errorMessage and " +
                            "generatedMethod");
                String ctxtActionWord = selection == PromptSelection.CONTEXT_ON_RESOLVE_FAIL ? "resolve" : "verify";
                prompt.append("When using dafny ").append(ctxtActionWord).append(", the below error is emitted and ").append(ctxtActionWord).append(" fails:\n\n");
                prompt.append(errorMessage).append("\n\n");
                prompt.append("Correct the error in code");
                if (!methodSig.isEmpty())
                    prompt.append(" by altering only the ").append(codeOrMethod).append(" body. Produce and show only the Dafny body, " +
                            "including the curly braces that surround it. Do not show the signature nor contract");
                prompt.append(". You must not use 'assume' anywhere in your code.");
                break;
            case CONTEXT_ON_ASSUME_USED_FAIL:
                if (generatedMethod == null || generatedMethod.isBlank())
                    throw new IllegalArgumentException("CONTEXT_ON_ASSUME_USED_FAIL requires generatedMethod");
                prompt.append("The ").append(codeOrMethod).append(" uses 'assume', but must not do so.");
                if (!methodSig.isEmpty())
                    prompt.append(" Correct the error by altering only the method body to not use 'assume'. Produce and show only the " +
                            "Dafny body, including the curly braces that surround it. Do not show the signature nor contract.");
                else
                    prompt.append(" Correct the error by altering the code to not include 'assume'.");
                prompt.append(" You must not use 'assume' anywhere in your code.");
                break;
            default:
                throw new UnsupportedOperationException("Unknown prompt type: " + selection);
        }
        int newLns = 0;
        for (int i = prompt.length() - 1; i >= 0 && prompt.charAt(i) == '\n'; newLns++, --i) ;
        prompt.setLength(prompt.length() - newLns);
        return prompt.toString();
    }


    private String turnGenAIResponseToDafnyProgram(String response) {
        StringBuilder sb = new StringBuilder();
        if (problem.dafny().functionalCode() != null) {
            sb.append(problem.dafny().functionalCode());
            sb.append("\n\n");
        }
        if (problem.dafny().methodSignature() == null || problem.dafny().methodSignature().isEmpty()) {
            log.info("Treating GenAIs response as a complete program as the problem statement has no method signature.");
            sb.append(response);
        } else {
            log.info("Treating GenAIs response as a partial method, not a complete program (Since, the problem spec has a method " +
                    "signature).");
            sb.append("method ").append(problem.dafny().methodSignature()).append("\n");
            problem.dafny().requires().forEach(a -> sb.append("\t").append("requires ").append(a).append("\n"));
            problem.dafny().ensures().forEach(a -> sb.append("\t").append("ensures ").append(a).append("\n"));
            sb.append(response);
        }
        return sb.toString();
    }

    private void saveAndCompileLaTeX(String tex) throws IOException, InterruptedException {
        File texDir = new File(problemDir, "tex");
        texDir.mkdirs();
        File texFile = new File(texDir, "experiment_output.tex");
        Files.writeString(texFile.toPath(), tex);
        ProcessBuilder pb = new ProcessBuilder("xelatex", "-interaction=nonstopmode", "-halt-on-error",
                texFile.getName());
        pb.directory(texDir);
        pb.redirectErrorStream(true);
        Process process = pb.start();
        Files.copy(process.getInputStream(), new File(texDir, "latex_output.log").toPath(), StandardCopyOption.REPLACE_EXISTING);
        int code = process.waitFor();
        if (code == 0) {
            log.info("Compilation of experiment report tex file successful");
        } else {
            log.log(Level.SEVERE, "Compilation of experiment report tex file failed. See log for details.");
        }


    }

    private String experimentInfoToTex(DafnyExperimentResult result) {
        StringBuilder sb = new StringBuilder();
        sb.append("""
                \\documentclass{article}
                \\usepackage{lmodern}
                \\usepackage{amsmath}
                \\usepackage{listings}
                \\usepackage{fullpage}
                \\usepackage{parskip}
                \\usepackage{xcolor}
                \\lstset{
                	basicstyle=\\ttfamily,
                	columns=fullflexible,
                	frame=single,
                	breaklines=true,
                	postbreak=\\mbox{\\textcolor{red}{$\\hookrightarrow$}\\space},
                }
                \\begin{document}
                """);
        sb.append("\\title{Experiment `").append(escapeLatex(this.problem.name())).append("' Results}\n");
        sb.append("""
                \\author{\\today}
                \\date{}
                \\maketitle
                """);
        sb.append("\\textbf{Experiment outcome: }").append(escapeLatex(result.outcome().toString())).append("\n");
        sb.append("\\\\\\textbf{Bad responses: }").append(result.badResponses()).append("\n");
        sb.append("\\\\\\textbf{Responses containing}~\\texttt{assume}~\\textbf{: }").append(result.responsesWithAssume()).append("\n");
        sb.append("\\\\\\textbf{Resolution attempts: }").append(result.resolutionAttempts()).append("\n");
        sb.append("\\\\\\textbf{Hard fails (resolution): }").append(result.hardFailedResolutions()).append("\n");
        sb.append("\\\\\\textbf{Soft fails (resolution): }").append(result.softFailedResolutions()).append("\n");
        sb.append("\\\\\\textbf{Verification attempts: }").append(result.verificationAttempts()).append("\n");
        sb.append("\\section*{Problem Specification}\n");
        sb.append("\\textbf{Problem name: }").append(escapeLatex(this.problem.name())).append("\n");
        sb.append("\\\\\\textbf{Natural language statement: }").append(escapeLatex(this.problem.statement())).append("\n");
        sb.append("\\\\\\textbf{Method signature: }").append(escapeLatex(this.problem.dafny().methodSignature())).append("\n");
        if (problem.dafny().ensures() != null && !problem.dafny().ensures().isEmpty()) {
            sb.append("\\subsection*{").append("Ensures").append("}\n");
            sb.append("\\begin{itemize}\n");
            for (String s : problem.dafny().ensures()) {
                sb.append("\\item \\texttt{").append(escapeLatex(s)).append("}\n");
            }
            sb.append("\\end{itemize}\n");
        }
        if (problem.dafny().requires() != null && !problem.dafny().requires().isEmpty()) { //Nasty code dup... Oops.
            sb.append("\\subsection*{").append("Requires").append("}\n");
            sb.append("\\begin{itemize}\n");
            for (String s : problem.dafny().requires()) {
                sb.append("\\item \\texttt{").append(escapeLatex(s)).append("}\n");
            }
            sb.append("\\end{itemize}\n");
        }
        if (problem.dafny().functionalCode() != null) {
            sb.append("\\subsection*{").append("Functional Code Given").append("}\n");
            sb.append("\\begin{lstlisting}\n");
            sb.append(problem.dafny().functionalCode()).append("\n");
            sb.append("\\end{lstlisting}\n");
        }

        sb.append("\\clearpage\n");
        sb.append("\\section*{GenAI interactions}\n");
        sb.append("Below you will find all interactions between the `user' (program) and the `assistant' (OpenAI).\n");
        for (TransactionUnion u : genAIMessages) {
            OpenAIMessageRole role = u.message().getRole();
            String title = role == OpenAIMessageRole.USER ? "Program $\\rightarrow$ GenAI" : "GenAI $\\rightarrow$ Program";
            sb.append("\\subsection*{").append(title).append("}\n");
            if (u.openAIResponseDetails() != null) {
                OpenAICompletionResponse resp = u.openAIResponseDetails();
                sb.append("\\textbf{System fingerprint: }").append(escapeLatex(resp.systemFingerprint())).append("\n");
                sb.append("\\\\\\textbf{ID: }").append(resp.id()).append("\n");
                sb.append("\\\\\\textbf{Model: }").append(escapeLatex(resp.model())).append("\n");
                sb.append("\\\\\\textbf{Created at: }").append(resp.createdAt()).append("\n");
                sb.append("\\\\\\textbf{Finish reason: }").append(escapeLatex(resp.choices().getFirst().finishReason())).append("\n");
                sb.append("\\\\\\textbf{Usage: }").append(resp.usage().promptTokens()).append(" tokens in, and ").append(resp.usage().completionTokens()).append(" tokens out").append("\n");
                if (u.message().getRefusal() != null)
                    sb.append("\\\\\\textbf{Refusal: }").append(escapeLatex(u.message().getRefusal())).append("\n");
                String out;
                try {
                    JsonObject o = GSON.fromJson(u.message().getContent(), JsonObject.class);
                    out = o.get("method_body").getAsString();
                } catch (Exception e) {
                    log.fine("Failed to parse GenAI response for LaTeX report generation. Dumping raw JSON");
                    out = u.message().getContent();
                    sb.append("\\\\\\textcolor{red}{\\textbf{The below is a raw response from GenAI that could not be parsed. It is " +
                            "likely that GenAI got 'stuck' in a loop and hit the pre-set token limit (i.e., finish reason is 'length')" +
                            ".}}\n");
                }
                sb.append("\\begin{lstlisting}\n");
                sb.append(out);
                sb.append("\n\\end{lstlisting}\n");//TODO dafny annotation
            } else {
                sb.append("\\begin{lstlisting}\n");
                sb.append(u.message().getContent());
                sb.append("\n\\end{lstlisting}\n");
            }
        }
        String prog = null;

        try {
            prog = Files.readString(new File(problemDir, "program.dfy").toPath());
        } catch (IOException e) {
            //Intentionally ignored.
        }
        sb.append("\\section*{Final Program}\n");
        if (prog != null) {
            sb.append("\\begin{lstlisting}\n");
            sb.append(prog);
            sb.append("\n\\end{lstlisting}\n");
        } else {
            sb.append("\\textit{No complete program emitted}\n");
        }

        DafnyExperimentTokenUsage usage = getUsageStats();
        sb.append("\\section*{").append("Total Token Usage").append("}\n");
        sb.append("\\textbf{Input tokens: }").append(usage.tokensInput()).append("\n");
        sb.append("\\\\\\textbf{Output tokens: }").append(usage.tokensOutput()).append("\n");
        sb.append("\\\\\\textbf{Reasoning tokens: }").append(usage.totalReasoningTokens()).append("\n");
        sb.append("\\\\\\textbf{Sum of `total tokens': }").append(usage.tokensTotal()).append("\n");


        sb.append("\\section*{Experiment Timings}\n");
        for (Map.Entry<String, EventTimer.EventTimingRecord> r : timer.getEvents().entrySet())
            sb.append("\\textbf{").append(escapeLatex(r.getKey())).append("} started at ")
                    .append(r.getValue().getStartTimeMs()).append(", ended at ")
                    .append(r.getValue().getEndTimeMs()).append(", lasting ")
                    .append(r.getValue().getDurationMs())
                    .append(String.format("ms (%.2f seconds)", r.getValue().getDurationMs() / 1000d))
                    .append("\n\\\\");
        sb.setLength(sb.length() - 2);//remove the last \\
        sb.append("\\end{document}\n");
        return sb.toString();
    }


    private String escapeLatex(String s) {
        if (s == null) return "null";
        if (s.isBlank()) return "";
        StringBuilder sb = new StringBuilder(s.length() * 2);
        for (int i = 0; i < s.length(); i++) {
            char ch = s.charAt(i);
            sb.append(switch (ch) {
                case '\\' -> "\\textbackslash{}";
                case '{', '}', '$', '%', '&', '#', '_' -> "\\" + ch;
                case '^' -> "\\^{}";
                case '~' -> "\\~{}";
                default -> "" + ch;
            });
        }
        return sb.toString();
    }

    private enum PromptSelection {
        INITIAL_PROMPT,
        RESOLVE_FAIL,
        VERIFY_FAIL,
        ASSUME_USED_FAIL,
        CONTEXT_ON_RESOLVE_FAIL,
        CONTEXT_ON_VERIFY_FAIL,
        CONTEXT_ON_ASSUME_USED_FAIL
    }

    private record TransactionUnion(OpenAIMessage message, OpenAICompletionResponse openAIResponseDetails) {
    }


}

