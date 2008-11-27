package ie.ucd.clops.logging;

import java.util.logging.Handler;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.logging.StreamHandler;

/**
 * Convenience class for working with a common logger.
 * 
 * @author Fintan
 */
public class CLOLogger {

  public static final Level DEFAULT_LEVEL = Level.INFO;
  
  private final static Logger logger;
  
  static {
    logger = Logger.getLogger("ie.ucd.clops");
    logger.setLevel(DEFAULT_LEVEL);
    //TODO - proper configuration of this
    logger.addHandler(new StreamHandler(System.out, new EndUserFormatter()));
    logger.setUseParentHandlers(false);
  }
    
  public static Logger getLogger() {
    return logger;
  }
  
  public static void setLogLevel(Level newLevel) {
    logger.setLevel(newLevel);
  }
  
  public static void removeAllHandlers() {
    for (Handler handler : logger.getHandlers()) {
      logger.removeHandler(handler);
    }
  }
  
    
}
