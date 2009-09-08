package ie.ucd.clops.runtime.errors;

import java.util.ArrayList;
import java.util.Set;

import static ie.ucd.clops.runtime.parser.GenericCLParser.ParseStep;

public class UnknownOptionError extends CLError {
  private Set<ArrayList<ParseStep>> parsings;
  private String suggested;

  public UnknownOptionError(int index, Set<ArrayList<ParseStep>> parsings) {
    super("Illegal option." , index);
    this.parsings = parsings;
  }

  public UnknownOptionError(int index, String suggestion) {
    super("Illegal option (" + suggestion + ")", index);
  }

  public Set<ArrayList<ParseStep>> getParsings() {
    return parsings;
  }
}
