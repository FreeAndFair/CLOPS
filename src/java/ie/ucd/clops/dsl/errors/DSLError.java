package ie.ucd.clops.dsl.errors;

import ie.ucd.clops.dsl.parser.SourceLocation;

public class DSLError extends DSLProblem {

  public DSLError(SourceLocation sourceLocation, String message) {
    super(sourceLocation, message);
  }

}
