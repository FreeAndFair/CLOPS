package ie.ucd.clops.dsl.errors;

import ie.ucd.clops.dsl.parser.SourceLocation;

public class UnknownIdentifierError extends DSLError {

  private static final String MESSAGE = "Unknown option or option group %s.";
  
  public UnknownIdentifierError(SourceLocation sourceLocation, String identifier) {
    super(sourceLocation, String.format(MESSAGE, identifier));
  }

}
