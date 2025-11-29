package click.nullpointer.genaidafny.openai.completion.common;

import com.google.gson.annotations.SerializedName;

public enum OpenAIMessageRole {
    @SerializedName("system") SYSTEM, @SerializedName("developer") DEVELOPER, @SerializedName("user") USER, @SerializedName("assistant") ASSISTANT;

    @Override
    public String toString() {
        return super.toString().toLowerCase();
    }
}