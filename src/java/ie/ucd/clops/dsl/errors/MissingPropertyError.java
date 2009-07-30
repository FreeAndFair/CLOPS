package ie.ucd.clops.dsl.errors;

import ie.ucd.clops.dsl.parser.SourceLocation;

public class MissingPropertyError  extends DSLError {

  public MissingPropertyError(SourceLocation sourceLocation, String option, String property) {
    super(sourceLocation, "The option '" + option 
        + "' requires the property '" + property + "'.");
  }

}
