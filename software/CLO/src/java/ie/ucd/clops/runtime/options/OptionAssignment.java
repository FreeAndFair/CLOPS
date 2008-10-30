package ie.ucd.clops.runtime.options;

/**
 * 
 * @author Fintan
 *
 */
public class OptionAssignment {

  private final String optionIdentifier;
  private final Object optionValue;
  
  public OptionAssignment(String optionIdentifier, Object optionValue) {
    this.optionIdentifier = optionIdentifier;
    this.optionValue = optionValue;
  }

  public String getOptionIdentifier() {
    return optionIdentifier;
  }

  public Object getOptionValue() {
    return optionValue;
  }

}
