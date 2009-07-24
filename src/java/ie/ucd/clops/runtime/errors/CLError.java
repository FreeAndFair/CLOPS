package ie.ucd.clops.runtime.errors;

public class CLError {

  private final String message;
  
  public CLError(String message) {
    this.message = message;
  }

  public String getMessage() {
    return message;
  }

  
}
