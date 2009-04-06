package ie.ucd.clops.dsl;

/**
 * An Exception that occurs when n OptionType is not known.
 * @author Fintan
 *
 */
public class UnknownOptionTypeException extends Exception {

  private static final long serialVersionUID = -5487962384756264239L;

  public UnknownOptionTypeException(String message) {
    super(message);
  }
  
}


