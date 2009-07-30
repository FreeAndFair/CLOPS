package ie.ucd.clops.runtime.errors;

public class CLWarning extends CLProblem {

  public CLWarning(String message) {
    super("warning: " + message);
  }

  public CLWarning(String message, int problemIndex) {
    super("warning: " + message, problemIndex);
  }
  
}
