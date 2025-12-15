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


    public static String lightStripCommentsAndStringsFromDafny(String input) {
        if (input == null || input.isBlank())
            return input;
        //TODO: test propperly.
        boolean inInlineComment = false;
        int inMultilineComment = 0;
        boolean inString = false;
        StringBuilder out = new StringBuilder();
        for (int i = 0; i < input.length(); i++) {
            char prev = i == 0 ? 0 : input.charAt(i - 1);
            char curr = input.charAt(i);
            char next = i == input.length() - 1 ? 0 : input.charAt(i + 1);
            if (curr == '"') {
                inString = !inString;
                continue;//Nasty, to skip closing "
            }
            if (inString) {
                continue;//Nasty.
            }

            //Surely not foolproof, e.g., //abc/*abc*//, but what can you do
            if (inMultilineComment != 0) {
                //if we find a second code block in a multiline one, we increment counter.
                if (curr == '/' && next == '*')
                    inMultilineComment++;
                else if (curr == '*' && next == '/' && prev != '/') {//accounts for /*/abc*/
                    inMultilineComment--;
                    //Nasty, but we need to skip the next /
                    i++;
                }
            } else if (inInlineComment) {
                if (curr == '\n') {
                    inInlineComment = false;
                }
            } else { //not in multiline block (even nested)
                if (curr == next && next == '/') {
                    inInlineComment = true;
                } else if (curr == '/' && next == '*') {
                    inMultilineComment = 1;
                } else {
                    out.append(curr);
                }
            }
        }
        return out.toString();
    }

}
