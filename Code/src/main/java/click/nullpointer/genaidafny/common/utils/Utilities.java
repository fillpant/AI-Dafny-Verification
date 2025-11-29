package click.nullpointer.genaidafny.common.utils;

import java.io.File;
import java.io.IOException;
import java.io.UncheckedIOException;
import java.sql.Date;
import java.text.SimpleDateFormat;
import java.util.logging.ConsoleHandler;
import java.util.logging.FileHandler;
import java.util.logging.Formatter;
import java.util.logging.Level;
import java.util.logging.LogRecord;
import java.util.logging.Logger;

public class Utilities {

    private static final SimpleDateFormat LOGGING_DATE_FORMAT = new SimpleDateFormat("dd/MM/yy HH:mm:ss.SSS");


    public static Logger createLogger(String name, File out) {
        Logger logger = Logger.getLogger(name);
        logger.setUseParentHandlers(false);
        logger.setLevel(Level.ALL);

        Formatter formatter = new Formatter() {
            @Override
            public String format(LogRecord record) {
                String timestamp = LOGGING_DATE_FORMAT.format(new Date(record.getMillis()));
                String loggerName = record.getLoggerName();
                String level = record.getLevel().getName();
                String message = formatMessage(record);
                String excepton = "";
                Throwable thrown = record.getThrown();
                if (thrown != null) {
                    StringBuilder builder = new StringBuilder();
                    builder.append("\n");
                    builder.append(thrown.getClass().getName()).append(": ").append(thrown.getMessage()).append('\n');
                    for (StackTraceElement ste : thrown.getStackTrace()) {
                        builder.append('\t').append("-> ").append(ste.toString()).append('\n');
                    }
                    excepton = builder.toString();
                }
                return String.format("[%s] [%s] [%s]: %s%s%n", timestamp, loggerName, level, message, excepton);
            }
        };

        ConsoleHandler handler = new ConsoleHandler();
        handler.setFormatter(formatter);
        handler.setLevel(Level.ALL);
        logger.addHandler(handler);
        try {
            FileHandler fileHandler = new FileHandler(out.getAbsolutePath(), true);
            fileHandler.setLevel(Level.ALL);
            fileHandler.setFormatter(formatter);
            logger.addHandler(fileHandler);
        } catch (IOException e) {
            throw new UncheckedIOException(e);
        }
        return logger;
    }
}
