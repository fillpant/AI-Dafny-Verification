package click.nullpointer.genaidafny.dafny.experiments.cache;

public class DummyDafnyExperimentCache implements IExperimentCache {
    @Override
    public String getCachedResponse(String prompt) {
        return null;
    }

    @Override
    public void cacheResponse(String prompt, String resp) {
    }
}
