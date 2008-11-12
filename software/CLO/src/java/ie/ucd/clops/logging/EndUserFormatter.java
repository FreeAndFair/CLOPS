package ie.ucd.clops.logging;

import java.util.logging.Formatter;
import java.util.logging.Handler;
import java.util.logging.LogRecord;

/**
 * 
 * @author fintan
 *
 */
public class EndUserFormatter extends Formatter {

  private String lineSeparator = (String) java.security.AccessController.doPrivileged(
      new sun.security.action.GetPropertyAction("line.separator"));
  
  @Override
  public String format(LogRecord record) {
    return record.getMessage() + lineSeparator;
  }

  @Override
  public synchronized String formatMessage(LogRecord record) {
    return super.formatMessage(record);
  }

  @Override
  public String getHead(Handler h) {
    return super.getHead(h);
  }

  @Override
  public String getTail(Handler h) {
    return super.getTail(h);
  }

  
  
}

