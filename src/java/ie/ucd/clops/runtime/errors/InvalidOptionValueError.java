package ie.ucd.clops.runtime.errors;

public class InvalidOptionValueError extends CLError {

  private final int position;
  
  public InvalidOptionValueError(int position, String message) {
    super(message);
    this.position = position;
  }

  public int getPosition() {
    return position;
  }

  
}
