package ie.ucd.clops.runtime.options;

/**
 * 
 * @author Fintan
 *
 */
public class InvalidOptionValueException extends Exception {

  private static final long serialVersionUID = -2338048349946693102L;

  public InvalidOptionValueException(String message, Throwable cause) {
    super(message, cause);
  }

  public InvalidOptionValueException(String message) {
    super(message);
  }
}
