package click.nullpointer.genaidafny.openai;

import click.nullpointer.genaidafny.openai.completion.OpenAICompletionManager;
import click.nullpointer.genaidafny.openai.completion.common.OpenAIMessage;
import click.nullpointer.genaidafny.openai.completion.common.OpenAIMessageRole;
import click.nullpointer.genaidafny.openai.completion.common.OpenAITextModel;
import click.nullpointer.genaidafny.openai.completion.requests.OpenAICompletionRequest;

import java.io.File;
import java.util.concurrent.ExecutionException;

public class Tests {

    public static void main(String[] args) throws ExecutionException, InterruptedException {
        OpenAICompletionManager comp = new OpenAICompletionManager("", new File("request_logs"));
        OpenAIMessage msg = new OpenAIMessage(OpenAIMessageRole.USER, "What is 3+892?");
        OpenAICompletionRequest request = new OpenAICompletionRequest(OpenAITextModel.GPT_4O_MINI, msg);
        request.setMaxCompletionTokens(200);
        request.setFrequencyPenalty(-2d);
        request.setTemperature(2.0);
        comp.submitCompletion(request)
                .handle((res, err) -> {
                    if (res != null) {
                        System.out.println(res);
                        System.out.println(res.choices().getFirst().message().getContent());
                    } else {
                        err.printStackTrace();
                    }
                    return null;
                }).join();

    }

}
