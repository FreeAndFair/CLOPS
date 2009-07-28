package ie.ucd.clops.dsl.errors;

import ie.ucd.clops.dsl.parser.SourceLocation;

public class UnusedIdentifierWarning extends DSLWarning {

  private static String MESSAGE_1 = "Option %s is not reachable from the format string.";
  private static String MESSAGE_2 = "Option group %s is not reachable from the format string.";
  
  public UnusedIdentifierWarning(SourceLocation sourceLocation, boolean option, String identifier) {
    super(sourceLocation, String.format(option ? MESSAGE_1 : MESSAGE_2, identifier));
  }

}
