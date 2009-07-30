package ie.ucd.clops.runtime.errors;

public class InvalidOptionValueError extends CLError {
 
  public InvalidOptionValueError(String message, int position) {
    super(message, position);
  }

  public InvalidOptionValueError(String message) {
    super(message);
  }
  
}
