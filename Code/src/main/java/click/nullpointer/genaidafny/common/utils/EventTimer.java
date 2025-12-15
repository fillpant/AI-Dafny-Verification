package click.nullpointer.genaidafny.common.utils;

import java.util.HashMap;
import java.util.Map;

public class EventTimer {
    private final Map<String, EventTimingRecord> events = new HashMap<>();
    private transient String lastKey;

    public EventTimingRecord startEvent(String name) {
        EventTimingRecord record = new EventTimingRecord(System.currentTimeMillis());
        events.put(name, record);
        return record;
    }

    public EventTimingRecord stopEvent(String name) {
        EventTimingRecord record = events.get(name);
        if (record == null)
            return null;
        record.setEndTimeMs(System.currentTimeMillis());
        lastKey = name;
        return record;
    }

    public EventTimingRecord getLastStoppedEvent() {
        if (lastKey == null)
            return null;
        return events.get(lastKey);
    }

    public Map<String, EventTimingRecord> getEvents() {
        return events;
    }

    public static class EventTimingRecord {
        private long startTimeMs;
        private long endTimeMs;
        private long durationMs;

        public EventTimingRecord(long startTimeMs) {
            this.startTimeMs = startTimeMs;
        }

        public long getStartTimeMs() {
            return startTimeMs;
        }

        public long getEndTimeMs() {
            return endTimeMs;
        }

        public long getDurationMs() {
            return durationMs;
        }

        private void setEndTimeMs(long endTimeMs) {
            this.endTimeMs = endTimeMs;
            this.durationMs = endTimeMs - startTimeMs;//for serialisation.
        }

    }

}
