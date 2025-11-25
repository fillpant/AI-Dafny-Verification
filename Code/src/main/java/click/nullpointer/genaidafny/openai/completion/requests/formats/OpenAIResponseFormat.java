package click.nullpointer.genaidafny.openai.completion.requests.formats;

public abstract class OpenAIResponseFormat {
        private String type;

        protected OpenAIResponseFormat(String type) {
            this.type = type;
        }
    }