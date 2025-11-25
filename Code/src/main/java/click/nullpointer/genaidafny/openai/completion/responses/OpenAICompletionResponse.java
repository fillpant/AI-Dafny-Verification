package click.nullpointer.genaidafny.openai.completion.responses;

import com.google.gson.annotations.SerializedName;

import java.util.List;

public record OpenAICompletionResponse(String id, @SerializedName("object") String objectType,
                                       @SerializedName("created") long createdAt, String model,
                                       List<OpenAIResponseChoice> choices, OpenAIUsage usage,
                                       @SerializedName("service_tier") String serviceTier,
                                       @SerializedName("system_fingerprint") String systemFingerprint) {


}

