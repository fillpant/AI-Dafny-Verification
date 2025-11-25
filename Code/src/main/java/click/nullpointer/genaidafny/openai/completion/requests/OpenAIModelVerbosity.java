package click.nullpointer.genaidafny.openai.completion.requests;

import com.google.gson.annotations.SerializedName;

public enum OpenAIModelVerbosity {
        @SerializedName("low") LOW, @SerializedName("medium") MEDIUM, @SerializedName("high") HIGH;

        @Override
        public String toString() {
            return super.toString().toLowerCase();
        }
    }