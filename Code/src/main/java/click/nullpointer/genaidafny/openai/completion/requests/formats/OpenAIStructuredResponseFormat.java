package click.nullpointer.genaidafny.openai.completion.requests.formats;

import com.google.gson.JsonObject;
import com.google.gson.annotations.SerializedName;

public class OpenAIStructuredResponseFormat extends OpenAIResponseFormat {
    @SerializedName("json_schema")
    private JsonObject schema;

    public OpenAIStructuredResponseFormat(JsonObject schema) {
        super("json_schema");
        this.schema = schema;
    }
}