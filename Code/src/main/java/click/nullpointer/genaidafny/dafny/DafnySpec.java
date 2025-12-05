package click.nullpointer.genaidafny.dafny;

import com.google.gson.annotations.SerializedName;

import java.util.List;

public record DafnySpec(@SerializedName("method_signature") String methodSignature,
                        @SerializedName("functional_code") String functionalCode, List<String> requires,
                        List<String> ensures) {
}
