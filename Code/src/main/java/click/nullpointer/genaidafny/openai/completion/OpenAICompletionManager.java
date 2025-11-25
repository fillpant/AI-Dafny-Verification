package click.nullpointer.genaidafny.openai.completion;

import click.nullpointer.genaidafny.openai.completion.requests.OpenAICompletionRequest;
import click.nullpointer.genaidafny.openai.completion.responses.OpenAICompletionResponse;
import click.nullpointer.genaidafny.openai.helpers.OpenAIRateLimiter;
import com.google.gson.Gson;
import com.google.gson.JsonObject;

import java.io.File;
import java.io.IOException;
import java.net.URI;
import java.net.http.HttpClient;
import java.net.http.HttpRequest;
import java.net.http.HttpResponse;
import java.nio.file.Files;
import java.util.concurrent.CompletableFuture;

public class OpenAICompletionManager {
    public static final String OPEN_AI_COMPLETIONS_URL = "https://api.openai.com/v1/chat/completions";
    private static final Gson GSON = new Gson().newBuilder().create();
    private static final Gson GSON_PRETTY = new Gson().newBuilder().setPrettyPrinting().create();
    private final HttpClient httpClient = HttpClient.newHttpClient();
    private final OpenAIRateLimiter rateLimiter;
    private final String openAIKey;
    private volatile boolean terminated = false;
    private File logDirectory;

    public OpenAICompletionManager(String openAIToken, File logDirectory) {
        if (logDirectory != null) {
            if (!logDirectory.exists())
                logDirectory.mkdirs();
            else {
                if (!logDirectory.isDirectory()) {
                    throw new IllegalArgumentException("logDirectory is not a directory");
                }
            }
        }
        this.logDirectory = logDirectory;
        this.rateLimiter = new OpenAIRateLimiter(OpenAIRateLimiter.RateLimitingPolicy.DELAY_REQUEST);
        this.openAIKey = openAIToken;
    }

    public synchronized CompletableFuture<OpenAICompletionResponse> submitCompletion(OpenAICompletionRequest request) {
        if (terminated) throw new IllegalStateException("Manager is no longer usable.");
        String json = GSON.toJson(request);
        HttpRequest req = baseRequest().POST(HttpRequest.BodyPublishers.ofString(json)).build();
        return rateLimiter.getRateLimitingBase().thenComposeAsync(x -> httpClient.sendAsync(req, HttpResponse.BodyHandlers.ofString())).thenApplyAsync(x -> {
                    rateLimiter.updateRateLimit(x.headers());
                    return x;
                }).thenApplyAsync(x -> {
                    if (x.statusCode() != 200)
                        throw new IllegalStateException("Got HTTP code " + x.statusCode() + " with body " + x.body());
                    return x.body();
                }).thenApplyAsync(x -> GSON.fromJson(x, OpenAICompletionResponse.class))
                .whenComplete((response, throwable) -> {
                    if (logDirectory != null) {
                        String name = response == null ? "failed_job_" + System.currentTimeMillis() + ".json" : "job_" + response.id() + ".json";
                        JsonObject data = new JsonObject();
                        data.add("request_to_gpt", GSON_PRETTY.toJsonTree(request));
                        if (response != null) data.add("response_from_gpt", GSON.toJsonTree(response));
                        else data.addProperty("errors", exceptionToString(throwable));
                        File interaction = new File(logDirectory, name);
                        try {
                            Files.writeString(interaction.toPath(), GSON_PRETTY.toJson(data));
                        } catch (IOException e) {
                            e.printStackTrace();
                        }
                    }
                });
    }

    private String exceptionToString(Throwable throwable) {
        StringBuilder sb = new StringBuilder();
        sb.append(throwable.getClass().toString() + ": " + throwable.getMessage());
        for (StackTraceElement ste : throwable.getStackTrace()) {
            sb.append("\n\t" + ste.toString());
        }
        return sb.toString();
    }


//    private void addPendingRequest(CompletableFuture<?> future) {
//        synchronized (pendingRequests) {
//            pendingRequests.add(future);
//        }
//    }
//
//    private void removePendingRequest(CompletableFuture<?> future) {
//        synchronized (pendingRequests) {
//            pendingRequests.remove(future);
//        }
//    }
//
//    public synchronized void terminate() {
//        terminated = true;
//        synchronized (pendingRequests) {
//            for (CompletableFuture<?> future : pendingRequests) {
//                future.join();
//            }
//        }
//        pendingRequests.clear();
//    }

    private HttpRequest.Builder baseRequest() {
        return HttpRequest.newBuilder().uri(URI.create(OPEN_AI_COMPLETIONS_URL)).header("Authorization", "Bearer " + openAIKey).header("Content-Type", "application/json");
    }

}
