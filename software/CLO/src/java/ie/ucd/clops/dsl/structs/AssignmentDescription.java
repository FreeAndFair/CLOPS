package ie.ucd.clops.dsl.structs;

/**
 * 
 * @author Fintan
 *
 */
public class AssignmentDescription {

  private final String optionIdentifier;
  private final String value;
  
  public AssignmentDescription(String optionIdentifier, String value) {
    this.optionIdentifier = optionIdentifier;
    this.value = value;
  }

  public String getOptionIdentifier() {
    return optionIdentifier;
  }

  public String getValue() {
    return value;
  }
  
}
