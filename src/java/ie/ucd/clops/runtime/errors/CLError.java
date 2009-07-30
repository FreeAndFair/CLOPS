package ie.ucd.clops.runtime.errors;

public class CLError extends CLProblem {

  public CLError(String message) {
    super(message);
  }

  public CLError(String message, int problemIndex) {
    super(message, problemIndex);
  }

}
