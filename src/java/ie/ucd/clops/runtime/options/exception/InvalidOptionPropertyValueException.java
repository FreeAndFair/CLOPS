package ie.ucd.clops.runtime.options.exception;

import ie.ucd.clops.runtime.ClopsInternalException;

/**
 * 
 * @author Fintan
 *
 */
public class InvalidOptionPropertyValueException extends ClopsInternalException {

  private static final long serialVersionUID = -7650183596977067164L;

  public InvalidOptionPropertyValueException(String message, Throwable cause) {
    super(message, cause);
  }

  public InvalidOptionPropertyValueException(String message) {
    super(message);
  }
}
