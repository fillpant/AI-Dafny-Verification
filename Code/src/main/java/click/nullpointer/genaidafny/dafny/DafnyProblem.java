package click.nullpointer.genaidafny.dafny;

import com.google.gson.annotations.SerializedName;

public record DafnyProblem(String name, @SerializedName("nat_lang_statement") String statement, DafnySpec dafny) {
}
