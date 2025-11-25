package click.nullpointer.genaidafny.openai.completion.responses;

import com.google.gson.annotations.SerializedName;

public record OpenAIUsage(@SerializedName("prompt_tokens") int promptTokens,
                          @SerializedName("completion_tokens") int completionTokens,
                          @SerializedName("total_tokens") int totalTokens,
                          @SerializedName("prompt_tokens_details") OpenAIPromptTokensDetails promptTokensDetails,
                          @SerializedName("completion_tokens_details") OpenAICompletionTokensDetails completionTokensDetails) {
    }