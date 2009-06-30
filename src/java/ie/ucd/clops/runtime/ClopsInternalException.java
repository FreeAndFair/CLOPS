package ie.ucd.clops.runtime;

public class ClopsInternalException extends RuntimeException {

  /** */
  private static final long serialVersionUID = 1L;
  public  ClopsInternalException(String message, Throwable cause) {
    super(message, cause);
  }

  public  ClopsInternalException(String message) {
    super(message);
  }
  public  ClopsInternalException() {
    super();
  }
}
