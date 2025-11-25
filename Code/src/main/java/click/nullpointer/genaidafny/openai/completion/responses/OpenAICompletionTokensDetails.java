package click.nullpointer.genaidafny.openai.completion.responses;

import com.google.gson.annotations.SerializedName;

public record OpenAICompletionTokensDetails(@SerializedName("reasoning_tokens") int reasoningTokens,
                                            @SerializedName("audio_tokens") int audioTokens,
                                            @SerializedName("accepted_prediction_tokens") int acceptedPredictionTokens,
                                            @SerializedName("rejected_prediction_tokens") int rejectedPredictionTokens) {
    }