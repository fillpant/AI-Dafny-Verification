package click.nullpointer.genaidafny.dafny.experiments;

import click.nullpointer.genaidafny.Main;
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
import java.util.Objects;
import java.util.concurrent.ExecutionException;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.stream.Collectors;

public class DafnyExperiment {
    private static final String INITIAL_PROMPT_STRUCTURE = "You are given the following task to perform in Dafny:\n\n%s\n\nThe signature should be:\n\n%s\n\nThe method should respect the following contract:\n\n%s\n\n%sProduce and show only the Dafny body of this method, including the curly braces that surround it. Do not show the signature nor contract.";
    private static final String RESOLVE_FAIL_PROMPT_STRUCTURE = "Consider the method \"%s\" shown below: \n\n%s\n\n When using dafny resolve, the below error is emitted and resolve fails: \n\n%s\n\nCorrect the error by altering only the method body. Produce and show only the Dafny body, including the curly braces that surround it. Do not show the signature nor contract.";
    private static final String VERIFY_FAIL_PROMPT_STRUCTURE = "Consider the method \"%s\" shown below: \n\n%s\n\n When using dafny verify, the below error is emitted and verify fails: \n\n%s\n\nCorrect the error by altering only the method body. Produce and show only the Dafny body, including the curly braces that surround it. Do not show the signature nor contract.";
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
        if (!Main.getConfig().containsKey(ConfigurationKeys.DISABLE_EXPERIMENT_CACHE))
            this.cache = new DafnyExperimentCache(new File(problemDir, "caches.json"));
        else
            this.cache = new DummyDafnyExperimentCache();
        log.info("Experiment created.");
    }

    public DafnyExperimentResult execute() {
        if (currentState != DafnyExperimentState.NOT_STARTED)
            throw new IllegalStateException("Experiment is no longer runnable.");
        currentState = DafnyExperimentState.RUNNING;
        DafnyExperimentOutcome outcome = DafnyExperimentOutcome.SUCCESS;
        log.info("Experiment started.");
        final int maxGenAIInteractions = Integer.parseInt(Main.getConfig().get(ConfigurationKeys.MAX_GEN_AI_INTERACTIONS));
        try {
            String prompt = constructAIPrompt();
            log.info("Using initial prompt: " + prompt);
            while (genAIInteractions < maxGenAIInteractions) {
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
                    prompt = constructResolutionPrompt(problem.dafny().methodSignature(), resolveOut.getFullScreenOutput(), method);
                    continue; //oops
                }
                log.info("Dafny resolution check passed.");
                log.info("Calling dafny to verify the generated method...");
                CLIProgramOutput verifyOut = DafnyCLIIntegrator.verify(new File(problemDir, "program.dfy"));
                logCLIResult(verifyOut);
                verificationAttempts++;
                if (verifyOut.exitCode() != 0) {
                    log.warning("Failed to verify the generated method. Preparing GenAI prompt to fix...");
                    prompt = constructVerificationPrompt(problem.dafny().methodSignature(), verifyOut.getFullScreenOutput(), method);
                    continue;
                }
                log.info("Dafny verification check passed.");
                break; //Poor code restructure.
            }
            if (maxGenAIInteractions <= genAIInteractions) {
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
            if (genAIInteractions >= maxGenAIInteractions) {
                outcome = verificationAttempts == 0 ? DafnyExperimentOutcome.FAILURE_RESOLVE : DafnyExperimentOutcome.FAILURE_VERIFY;
            }
        }
        DafnyExperimentResult result = new DafnyExperimentResult(outcome, verificationAttempts, resolutionAttempts);
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

    private String constructVerificationPrompt(String methodSig, String fullScreenOutput, String fullMethod) {
        return VERIFY_FAIL_PROMPT_STRUCTURE.formatted(methodSig, fullMethod, fullScreenOutput);
    }

    private String constructResolutionPrompt(String methodSig, String fullScreenOutput, String fullMethod) throws ExecutionException, InterruptedException {
        return RESOLVE_FAIL_PROMPT_STRUCTURE.formatted(methodSig, fullMethod, fullScreenOutput);
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

    private String constructAIPrompt() {
        StringBuilder contract = new StringBuilder();
        contract.append(problem.dafny().requires().stream().map(a -> "requires " + a).collect(Collectors.joining(", ")));
        if (!problem.dafny().requires().isEmpty() && !problem.dafny().ensures().isEmpty())
            contract.append(", ");
        contract.append(problem.dafny().ensures().stream().map(a -> "ensures " + a).collect(Collectors.joining(", ")));
        String functionalCode = "";
        if (problem.dafny().functionalCode() != null) {
            functionalCode = "The contract uses the following dafny code:\n\n" + problem.dafny().functionalCode() + "\n\n";
        }
        return String.format(INITIAL_PROMPT_STRUCTURE, problem.statement(), "method " + problem.dafny().methodSignature(), contract.toString(), functionalCode);
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
        OpenAICompletionRequest req = new OpenAICompletionRequest(OpenAITextModel.valueOf(Main.getConfig().get(ConfigurationKeys.GEN_AI_MODEL)), context.toArray(new OpenAIMessage[0]));
        req.setResponseFormat(new OpenAIStructuredResponseFormat(STRUCTURED_RESPONSE_JSON));
        int maxTokens = Integer.parseInt(Main.getConfig().get(ConfigurationKeys.MAX_GEN_AI_OUTPUT_TOKENS));
        if (maxTokens > 0) {
            log.fine("Setting max tokens to " + maxTokens);
            req.setMaxCompletionTokens(maxTokens);
        }
        log.fine("Using model " + req.getModel() + ". Awaiting response...");
        OpenAICompletionResponse oaiResp = completionManager.submitCompletion(req).get();
        OpenAIMessage responseMsg = oaiResp.choices().getFirst().message();

        genAIMessages.add(new TransactionUnion(responseMsg, oaiResp));
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
        if (problem.dafny().functionalCode() != null) {
            sb.append(problem.dafny().functionalCode());
            sb.append("\n\n");
        }
        sb.append("method ").append(problem.dafny().methodSignature()).append("\n");
        problem.dafny().requires().forEach(a -> sb.append("\t").append("requires ").append(a).append("\n"));
        problem.dafny().ensures().forEach(a -> sb.append("\t").append("ensures ").append(a).append("\n"));
        sb.append(response);
        return sb.toString();
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
        sb.append("\\\\\\textbf{Resolution attempts: }").append(result.resolutionAttempts()).append("\n");
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
                    sb.append("\\textcolor{red}{\\textbf{The below is a raw response from GenAI that could not be parsed. It is likely that GenAI got 'stuck' in a loop and hit the pre-set token limit.}}\n");
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
        if (prog != null) {
            sb.append("\\section*{Final Program}\n");
            sb.append("\\begin{lstlisting}\n");
            sb.append(prog);
            sb.append("\\end{lstlisting}\n");
        }
        sb.append("\\end{document}\n");
        return sb.toString();
    }

    private String escapeLatex(String s) {
        if (s == null || s.isEmpty()) return "";
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

    private record TransactionUnion(OpenAIMessage message, OpenAICompletionResponse openAIResponseDetails) {
    }
}

