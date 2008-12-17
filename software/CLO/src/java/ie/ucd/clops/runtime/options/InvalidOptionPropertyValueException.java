package ie.ucd.clops.runtime.options;

/**
 * 
 * @author Fintan
 *
 */
public class InvalidOptionPropertyValueException extends Exception {

  private static final long serialVersionUID = -7650183596977067164L;

  public InvalidOptionPropertyValueException(String message, Throwable cause) {
    super(message, cause);
  }

  public InvalidOptionPropertyValueException(String message) {
    super(message);
  }
}
