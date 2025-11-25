package click.nullpointer.genaidafny.openai.completion.common;

public enum OpenAITextModel {
        GPT_5_1("gpt-5.1"),
        GPT_5("gpt-5"),
        GPT_5_MINI("gpt-5-mini"),
        GPT_5_NANO("gpt-5-nano"),
        GPT_5_1_CHAT_LATEST("gpt-5.1-chat-latest"),
        GPT_5_CHAT_LATEST("gpt-5-chat-latest"),
        GPT_5_1_CODEX("gpt-5.1-codex"),
        GPT_5_CODEX("gpt-5-codex"),
        GPT_5_PRO("gpt-5-pro"),
        GPT_4_1("gpt-4.1"),
        GPT_4_1_MINI("gpt-4.1-mini"),
        GPT_4_1_NANO("gpt-4.1-nano"),
        GPT_4O("gpt-4o"),
        GPT_4O_2024_05_13("gpt-4o-2024-05-13"),
        GPT_4O_MINI("gpt-4o-mini"),
        GPT_REALTIME("gpt-realtime"),
        GPT_REALTIME_MINI("gpt-realtime-mini"),
        GPT_4O_REALTIME_PREVIEW("gpt-4o-realtime-preview"),
        GPT_4O_MINI_REALTIME_PREVIEW("gpt-4o-mini-realtime-preview"),
        GPT_AUDIO("gpt-audio"),
        GPT_AUDIO_MINI("gpt-audio-mini"),
        GPT_4O_AUDIO_PREVIEW("gpt-4o-audio-preview"),
        GPT_4O_MINI_AUDIO_PREVIEW("gpt-4o-mini-audio-preview"),
        O1("o1"),
        O1_PRO("o1-pro"),
        O3_PRO("o3-pro"),
        O3("o3"),
        O3_DEEP_RESEARCH("o3-deep-research"),
        O4_MINI("o4-mini"),
        O4_MINI_DEEP_RESEARCH("o4-mini-deep-research"),
        O3_MINI("o3-mini"),
        O1_MINI("o1-mini"),
        GPT_5_1_CODEX_MINI("gpt-5.1-codex-mini"),
        CODEX_MINI_LATEST("codex-mini-latest"),
        GPT_5_SEARCH_API("gpt-5-search-api"),
        GPT_4O_MINI_SEARCH_PREVIEW("gpt-4o-mini-search-preview"),
        GPT_4O_SEARCH_PREVIEW("gpt-4o-search-preview");

        private final String value;

        OpenAITextModel(String value) {
            this.value = value;
        }

        public String getValue() {
            return value;
        }
    }