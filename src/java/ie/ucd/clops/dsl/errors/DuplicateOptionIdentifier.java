package ie.ucd.clops.dsl.errors;

import ie.ucd.clops.dsl.parser.SourceLocation;

public class DuplicateOptionIdentifier extends DSLError {

  private static final String MESSAGE = "Duplicate use of identifier %s. Other use %s:%s:%s.";
  
  public DuplicateOptionIdentifier(SourceLocation sourceLocation, String identifier, SourceLocation otherUse) {
    super(sourceLocation, String.format(MESSAGE, identifier, otherUse.getFilePath(), otherUse.getLineNumber(), otherUse.getCharPositionInLine()));
  }

  
  
}
