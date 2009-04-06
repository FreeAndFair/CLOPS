package ie.ucd.clops.logging;

import java.util.logging.Formatter;
import java.util.logging.LogRecord;

/**
 * Formats log messages for end users.
 * These log messages are typically 1 line, and contain no extraneous log 
 * information such as time, severity, creating class, etc.
 * In essence it provides the originally given log message.
 * 
 * @author Fintan
 */
public class EndUserFormatter extends Formatter {

  private String lineSeparator = System.getProperty("line.separator");
  
  @Override
  public String format(LogRecord record) {
    return record.getMessage() + lineSeparator;
  }

}

