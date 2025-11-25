package click.nullpointer.genaidafny.openai.completion.responses;

import com.google.gson.annotations.SerializedName;

public record OpenAIPromptTokensDetails(@SerializedName("cached_tokens") int cachedTokens,
                                        @SerializedName("audio_tokens") int audioTokens) {
    }