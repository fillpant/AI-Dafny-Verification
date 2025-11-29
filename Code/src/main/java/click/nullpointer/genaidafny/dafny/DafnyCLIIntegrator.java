package click.nullpointer.genaidafny.dafny;

import java.io.BufferedReader;
import java.io.File;
import java.io.IOException;
import java.io.InputStreamReader;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.stream.Collectors;

public final class DafnyCLIIntegrator {

    private DafnyCLIIntegrator() {
    }

    public static CLIProgramOutput verify(File dfyFile, String... flags) throws IOException, InterruptedException {
        //dafny verify --flag-1 --flag-2 <path/to/file>
        List<String> args = new ArrayList<>();
        args.add("dafny");
        args.add("verify");
        args.add(dfyFile.getAbsolutePath());
        args.addAll(Arrays.asList(flags));
        ProcessBuilder pb = new ProcessBuilder(args);
        Process proc = pb.start();
        proc.waitFor();
        int exitCode = proc.exitValue();
        String stdout, stderr;
        try (BufferedReader out = new BufferedReader(new InputStreamReader(proc.getInputStream()));
             BufferedReader errOut = new BufferedReader(new InputStreamReader(proc.getErrorStream()))) {
            stdout = out.lines().collect(Collectors.joining("\n"));
            stderr = errOut.lines().collect(Collectors.joining("\n"));
        }
        return new CLIProgramOutput(stdout, stderr, exitCode);
    }

    public static CLIProgramOutput resolve(File dfyFile, String... flags) throws IOException, InterruptedException {
        //dafny resolve --flag-1 --flag-2 <path/to/file>
        List<String> args = new ArrayList<>();
        args.add("dafny");
        args.add("resolve");
        args.add(dfyFile.getAbsolutePath());
        args.addAll(Arrays.asList(flags));
        ProcessBuilder pb = new ProcessBuilder(args);
        Process proc = pb.start();
        proc.waitFor();
        int exitCode = proc.exitValue();
        String stdout, stderr;
        try (BufferedReader out = new BufferedReader(new InputStreamReader(proc.getInputStream()));
             BufferedReader errOut = new BufferedReader(new InputStreamReader(proc.getErrorStream()))) {
            stdout = out.lines().collect(Collectors.joining("\n"));
            stderr = errOut.lines().collect(Collectors.joining("\n"));
        }
        return new CLIProgramOutput(stdout, stderr, exitCode);
    }

}
