package ie.ucd.clops.dsl.errors;

import ie.ucd.clops.dsl.parser.SourceLocation;
import ie.ucd.clops.util.SourceReader;

import java.io.PrintStream;

public class DSLProblem implements Comparable<DSLProblem> {

  private final SourceLocation sourceLocation;
  private final String message;
  
  public DSLProblem(SourceLocation sourceLocation, String message) {
    super();
    this.sourceLocation = sourceLocation;
    this.message = message;
  }
  
  public SourceLocation getSourceLocation() {
    return sourceLocation;
  }

  public String getMessage() {
    return message;
  }

  public void printToStream(PrintStream ps) {
    printStart(ps);
    printMessage(ps);
    printSourcePosition(ps);
  }
  
  public void printStart(PrintStream ps) {
    if (sourceLocation != null) {
      ps.print(sourceLocation.getSourceFilePath());
      ps.print(':');

      if (sourceLocation.getLineNumber() > 0) {
        ps.print(sourceLocation.getLineNumber());
        ps.print(": ");
      } else {
        ps.print(' ');
      }
    } 
  }
  
  public void printMessage(PrintStream ps) {
    ps.println(getMessage());
  }
  
  public void printSourcePosition(PrintStream ps) {
    String sourceLine = getSourceLine();
    if (sourceLocation != null && sourceLocation.getCharPositionInLine() >= 0 && sourceLine != null) {

      int tabCount = 0;
      StringBuilder sb = new StringBuilder();
      for (int i=0; i < sourceLine.length(); i++) {
        char c = sourceLine.charAt(i);
        if (c == '\t') {
          sb.append("  ");
          if (i < sourceLocation.getCharPositionInLine()) {
            tabCount++;
          }
        } else {
          sb.append(c);
        }
      }

      ps.println(sb.toString());

      ps.println(getErrorPosition(sourceLocation.getCharPositionInLine() + tabCount));
    }
  }
  
  private String getSourceLine() {
    if (sourceLocation == null || sourceLocation.getLineNumber() <= 0) {
      return null;
    }
    return SourceReader.getInstance().getSource(sourceLocation.getSourceFile(), sourceLocation.getLineNumber());
  }
  
  /**
   * Returns a String which simply contains a caret character to indicate the location of
   * the error.
   * @param caretPosition The character position of the error.
   * @return A String to indicate the position of the error.
   */
  private static String getErrorPosition(int caretPosition) {
    StringBuilder sb = new StringBuilder();
    for (int i=0; i < caretPosition; i++) {
      sb.append(' ');
    }
    sb.append('^');
    return sb.toString();
  }

  @Override
  public int compareTo(DSLProblem o) {
    if (this.sourceLocation == null) {
      return o.sourceLocation == null ? (this==o ? 0 : -1) : -1;
    }
    int compare = this.sourceLocation.compareTo(o.sourceLocation);

    if (compare != 0) {
      return compare;
    } else {
      return this == o ? 0 : -1;
    }
  }
  
  
  
}
