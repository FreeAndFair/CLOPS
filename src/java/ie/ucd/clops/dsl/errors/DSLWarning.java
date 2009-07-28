package ie.ucd.clops.dsl.errors;

import java.io.PrintStream;

import ie.ucd.clops.dsl.parser.SourceLocation;

public class DSLWarning extends DSLProblem {

  public DSLWarning(SourceLocation sourceLocation, String message) {
    super(sourceLocation, message);
  }

  @Override
  public void printStart(PrintStream ps) {
    super.printStart(ps);
    ps.print("warning: ");
  }

  

}
