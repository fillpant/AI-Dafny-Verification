package click.nullpointer.genaidafny.dafny.experiments;

import com.google.gson.Gson;
import com.google.gson.JsonObject;

import java.io.File;
import java.io.IOException;
import java.lang.ref.WeakReference;
import java.nio.file.Files;

public class DafnyExperimentCache {
    private static final Gson GSON = new Gson();
    private final File backing;
    private WeakReference<JsonObject> loadedCache;

    public DafnyExperimentCache(File f) {
        this.backing = f;
    }

    public synchronized String getCachedResponse(String prompt) {
        JsonObject cache = loadCache();
        if (cache.has("prompts")) {
            JsonObject prompts = cache.get("prompts").getAsJsonObject();
            if (prompts.has(prompt)) {
                return prompts.get(prompt).getAsString();
            }
        }
        return null;
    }

    private JsonObject loadCache() {
        JsonObject obj = loadedCache == null ? null : loadedCache.get();
        if (obj == null) {
            if (backing != null && backing.length() > 0) {
                try {
                    JsonObject o = GSON.fromJson(Files.readString(backing.toPath()), JsonObject.class);
                    loadedCache = new WeakReference<>(o);
                    return o;
                } catch (IOException e) {
                    e.printStackTrace(); //Bad bad...
                }
            } else {
                JsonObject n = new JsonObject();
                loadedCache = new WeakReference<>(n);
                return n;
            }
        } else {
            return obj;
        }
        return null;
    }

    private synchronized void saveCache() {
        JsonObject obj;
        if (loadedCache == null || (obj = loadCache()) == null)
            return;
        String s = GSON.toJson(obj);
        try {
            Files.writeString(backing.toPath(), s);
        } catch (IOException e) {
            e.printStackTrace();
            //bad again, but this is a cache, if it fials it fails.
        }
    }

    public synchronized void cacheResponse(String prompt, String resp) {
        JsonObject cache = loadCache();
        JsonObject prompts;
        if (!cache.has("prompts")) prompts = new JsonObject();
        else prompts = cache.get("prompts").getAsJsonObject();
        prompts.addProperty(prompt, resp);
        cache.add("prompts", prompts);
        saveCache();
    }
}
