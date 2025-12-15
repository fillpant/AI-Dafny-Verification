package click.nullpointer.genaidafny.openai.completion.requests;

public enum OpenAIReasoningModelEffort {
    NONE, MINIMAL, LOW, MEDIUM, HIGH, XHIGH;

    public static OpenAIReasoningModelEffort getByValue(String r) {
        if (r != null)
            for (OpenAIReasoningModelEffort rr : values()) {
                if (rr.toString().equals(r)) {
                    return rr;
                }
            }
        return null;
    }

    @Override
    public String toString() {
        return super.toString().toLowerCase();
    }
}
