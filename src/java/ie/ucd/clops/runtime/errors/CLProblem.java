package ie.ucd.clops.runtime.errors;

import ie.ucd.clops.util.StringUtil;

import java.io.PrintStream;

public class CLProblem implements Comparable<CLProblem> {

  public static final int UNKNOWN_INDEX = -1;
  
  private final String message;
  private final int problemIndex;
  
  public CLProblem(String message) {
    this(message, UNKNOWN_INDEX);
  }
  
  public CLProblem(String message, int problemIndex) {
    this.message = message;
    this.problemIndex = problemIndex;
  }

  public String getMessage() {
    return message;
  }

  public int getProblemIndex() {
    return problemIndex;
  }

  public void printToStream(PrintStream ps, String commandLine) {
    ps.println(getMessage());
    if (problemIndex != UNKNOWN_INDEX && commandLine != null) {
      ps.println(commandLine);
      ps.println(StringUtil.getErrorPosition(problemIndex));
    }
  }

  @Override
  public int compareTo(CLProblem o) {
    if (o.problemIndex == UNKNOWN_INDEX) {
      return -1;
    } else if (this.problemIndex == UNKNOWN_INDEX) {
      return 1;
    } else {
      int diff = this.problemIndex - this.problemIndex;
      return diff == 0 ? -1 : diff;
    }
  }
  
}
