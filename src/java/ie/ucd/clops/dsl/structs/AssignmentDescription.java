package ie.ucd.clops.dsl.structs;

/**
 * 
 * @author Fintan
 *
 */
public class AssignmentDescription {

  private static int count = 1;
  
  private final String optionIdentifier;
  private String value;
  private final String id;
  
  public AssignmentDescription(String optionIdentifier, String value) {
    this.optionIdentifier = optionIdentifier;
    this.value = value;
    this.id = (count++) + "";
  }

  public String getOptionIdentifier() {
    return optionIdentifier;
  }

  public String getValue() {
    return value;
  }
  
  public String getId() {
    return id;
  }
  
  public void processPlaceholders(RuleStoreDescription dslInfo) {
    value = RuleDescription.processPlaceholders(value, dslInfo);
  }
  
}
