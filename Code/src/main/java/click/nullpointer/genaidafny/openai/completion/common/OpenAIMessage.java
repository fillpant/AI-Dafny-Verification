package click.nullpointer.genaidafny.openai.completion.common;

import java.util.Collections;
import java.util.List;

public class OpenAIMessage {
    private OpenAIMessageRole role;
    private String content;
    private String refusal;
    private List<OpenAIMessageAnnotation> annotations;

    public OpenAIMessage(OpenAIMessageRole role, String content) {
        this.role = role;
        this.content = content;
    }

    public OpenAIMessageRole getRole() {
        return role;
    }

    public void setRole(OpenAIMessageRole role) {
        this.role = role;
    }

    public String getContent() {
        return content;
    }

    public void setContent(String message) {
        this.content = message;
    }

    public String getRefusal() {
        return refusal;
    }


    public List<OpenAIMessageAnnotation> getAnnotations() {
        return Collections.unmodifiableList(annotations);
    }

}