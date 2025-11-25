package click.nullpointer.genaidafny.openai.completion.responses;

import click.nullpointer.genaidafny.openai.completion.common.OpenAIMessage;
import com.google.gson.annotations.SerializedName;

public record OpenAIResponseChoice(int index, OpenAIMessage message,
                                   @SerializedName("finish_reason") String finishReason) {
    }