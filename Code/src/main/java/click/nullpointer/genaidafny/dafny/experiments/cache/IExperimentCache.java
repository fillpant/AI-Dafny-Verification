package click.nullpointer.genaidafny.dafny.experiments.cache;

public interface IExperimentCache {

    String getCachedResponse(String prompt);

    void cacheResponse(String prompt, String resp);
}
