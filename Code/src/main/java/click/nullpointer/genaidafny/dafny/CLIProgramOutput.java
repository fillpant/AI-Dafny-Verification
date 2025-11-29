package click.nullpointer.genaidafny.dafny;

public record CLIProgramOutput(String stdout, String stderr, int exitCode) {
    public String getFullScreenOutput() {
        StringBuilder output = new StringBuilder();
        if (stdout != null) output.append(stdout);
        if (stderr != null) output.append(stderr);
        return output.toString();
    }
}
