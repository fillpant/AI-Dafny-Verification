package click.nullpointer.genaidafny.openai.completion.requests;

import click.nullpointer.genaidafny.openai.completion.common.OpenAIMessage;
import click.nullpointer.genaidafny.openai.completion.common.OpenAITextModel;
import click.nullpointer.genaidafny.openai.completion.requests.formats.OpenAIResponseFormat;
import click.nullpointer.genaidafny.openai.completion.requests.formats.OpenAITextResponseFormat;
import com.google.gson.annotations.SerializedName;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;

//see https://platform.openai.com/docs/api-reference/chat/create
public class OpenAICompletionRequest {
    private String model;
    private List<OpenAIMessage> messages;
    private Double temperature;
    private OpenAIModelVerbosity verbosity;
    @SerializedName("top_p")
    private Double topP;
    @SerializedName("n")
    private Integer completionCountN;
    @SerializedName("max_completion_tokens")
    private Integer maxCompletionTokens;
    @SerializedName("presence_penalty")
    private Double presencePenalty;
    @SerializedName("reasoning_effort")
    private String reasoningEffort;
    @SerializedName("frequency_penalty")
    private Double frequencyPenalty;
    @SerializedName("response_format")
    private OpenAIResponseFormat responseFormat = new OpenAITextResponseFormat();


    public OpenAICompletionRequest(String model, OpenAIMessage... messages) {
        this.model = model;
        this.messages = new ArrayList<>(Arrays.asList(messages));
    }

    public OpenAICompletionRequest(OpenAITextModel model, OpenAIMessage... messages) {
        this(model.getValue(), messages);
    }

    public Integer getMaxCompletionTokens() {
        return maxCompletionTokens;
    }

    public void setMaxCompletionTokens(Integer maxCompletionTokens) {
        this.maxCompletionTokens = maxCompletionTokens;
    }

    public String getModel() {
        return model;
    }

    public void setModel(OpenAITextModel model) {
        this.model = model.getValue();
    }

    public void setModel(String model) {
        this.model = model;
    }

    public void setReasoningEffort(OpenAIReasoningModelEffort reasoningEffort) {
        if (!OpenAITextModel.fromValue(model).isReasoning())
            throw new IllegalArgumentException("reasoningEffort is not supported for non-reasoning model: " + model);
        this.reasoningEffort = reasoningEffort.toString();
    }

    public OpenAIReasoningModelEffort getReasoningEffort() {
        return OpenAIReasoningModelEffort.getByValue(reasoningEffort);
    }

    public Double getTemperature() {
        return temperature;
    }

    public void setTemperature(Double temperature) {
        this.temperature = temperature;
    }

    public Double getTopP() {
        return topP;
    }

    public void setTopP(Double topP) {
        this.topP = topP;
    }

    public Integer getCompletionCountN() {
        return completionCountN;
    }

    public void setCompletionCountN(Integer completionCountN) {
        this.completionCountN = completionCountN;
    }

    public Double getPresencePenalty() {
        return presencePenalty;
    }

    public void setPresencePenalty(Double presencePenalty) {
        this.presencePenalty = presencePenalty;
    }

    public Double getFrequencyPenalty() {
        return frequencyPenalty;
    }

    public void setFrequencyPenalty(Double frequencyPenalty) {
        this.frequencyPenalty = frequencyPenalty;
    }

    public List<OpenAIMessage> getMessages() {
        return Collections.unmodifiableList(messages);
    }

    public void addMessage(OpenAIMessage message) {
        messages.add(message);
    }

    public void setResponseFormat(OpenAIResponseFormat responseFormat) {
        this.responseFormat = responseFormat;
    }

    public void setVerbosity(OpenAIModelVerbosity verbosity) {
        this.verbosity = verbosity;
    }

    public OpenAIModelVerbosity getVerbosity() {
        return verbosity;
    }

    public void validate() {
        if (model == null || model.isEmpty()) {
            throw new IllegalArgumentException("Model is required.");
        }
        if (messages == null || messages.isEmpty()) {
            throw new IllegalArgumentException("At least one message is required.");
        }
        for (OpenAIMessage msg : messages) {
            if (msg.getRole() == null) {
                throw new IllegalArgumentException("Message role cannot be null.");
            }
            if (msg.getContent() == null || msg.getContent().isEmpty()) {
                throw new IllegalArgumentException("Message content cannot be empty.");
            }
        }
        if (temperature != null && (temperature < 0 || temperature > 2)) {
            throw new IllegalArgumentException("Temperature must be between 0 and 2.");
        }
        if (topP != null && (topP < 0 || topP > 1)) {
            throw new IllegalArgumentException("top_p must be between 0 and 1.");
        }
        if (topP != null && temperature != null) {
            throw new IllegalArgumentException("top_p and temperature must not be both set at the same time.");
        }
        if (presencePenalty != null && (presencePenalty < -2 || presencePenalty > 2)) {
            throw new IllegalArgumentException("Presence penalty must be between -2 and 2.");
        }
        if (frequencyPenalty != null && (frequencyPenalty < -2 || frequencyPenalty > 2)) {
            throw new IllegalArgumentException("Frequency penalty must be between -2 and 2.");
        }
    }


}
