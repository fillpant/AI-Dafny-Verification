package click.nullpointer.genaidafny.openai.completion.common;

import com.google.gson.annotations.SerializedName;

public record OpenAIMessageAnnotation (String type, @SerializedName("url_citation") OpenAIURLCitation urlCitation){
    public record OpenAIURLCitation (@SerializedName("start_index") int startIndex, @SerializedName("end_index") int endIndex, String tite, String url){

    }
}
