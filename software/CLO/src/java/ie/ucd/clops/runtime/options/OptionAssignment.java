package ie.ucd.clops.runtime.options;

/**
 * 
 * @author Fintan
 *
 */
public class OptionAssignment {

  private final String optionIdentifier;
  private final String optionValue;
  
  public OptionAssignment(String optionIdentifier, String optionValue) {
    this.optionIdentifier = optionIdentifier;
    this.optionValue = optionValue;
  }

  public String getOptionIdentifier() {
    return optionIdentifier;
  }

  public String getOptionValue() {
    return optionValue;
  }

  @Override
  public String toString() {
    return optionIdentifier + ":=" + optionValue;
  }  
  
}
