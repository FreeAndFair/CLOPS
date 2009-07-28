package ie.ucd.clops.dsl.errors;

import ie.ucd.clops.dsl.parser.SourceLocation;

public class PropertyValueError extends DSLError {

  private static final String MESSAGE = "Invalid value for property %s on option %s. %s";
  
  public PropertyValueError(SourceLocation sourceLocation, String propertyName, String optionName, String errorMessage) {
    super(sourceLocation, String.format(MESSAGE, propertyName, optionName, errorMessage));
  }

}
