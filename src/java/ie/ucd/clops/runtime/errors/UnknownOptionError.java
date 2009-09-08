package ie.ucd.clops.runtime.errors;

import java.util.ArrayList;
import java.util.Set;

import static ie.ucd.clops.runtime.parser.GenericCLParser.ParseStep;

public class UnknownOptionError extends CLError {
  private Set<ArrayList<ParseStep>> parsings;

  public UnknownOptionError(int index, Set<ArrayList<ParseStep>> parsings, String suggestion) {
    super("Illegal option (" + suggestion + ")", index);
    this.parsings = parsings;
  }

  public Set<ArrayList<ParseStep>> getParsings() {
    return parsings;
  }
}
