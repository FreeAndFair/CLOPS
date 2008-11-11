package ie.ucd.clops.runtime.options;

import java.util.HashSet;
import java.util.Set;

/**
 * 
 * @author Fintan
 *
 */
public class StringEnumOption extends StringOption {

  private final Set<String> choices;
  private boolean caseSensitive;
  
  public StringEnumOption(String identifier, Set<String> aliases) {
    super(identifier, aliases);
    choices = new HashSet<String>();
    caseSensitive = false;
  }

  public StringEnumOption(String identifier) {
    super(identifier);
    choices = new HashSet<String>();
    caseSensitive = false;
  }

  public void addEnumChoice(String choice) {
    choices.add(choice);
  }

  @Override
  public void set(Object value) throws InvalidOptionValueException {
    if (value instanceof String) {
      for (String choice : choices) {
        String val = (String)value;
        if ((caseSensitive && choice.equals(value)) || choice.equalsIgnoreCase(val)) {
          super.set(value);
          return;
        }
      }
      throw new InvalidOptionValueException(value + " is not an allowed choice.");
    } else {
      throw new InvalidOptionValueException(value + " is not a String.");
    }
  }

  @Override
  public boolean acceptsProperty(String propertyName) {
    if (propertyName.equalsIgnoreCase("choices") ||  propertyName.equalsIgnoreCase("casesensitive")) {
      return true;
    } else {
      return super.acceptsProperty(propertyName);
    }
  }

  @Override
  public void setProperty(String propertyName, String propertyValue)
      throws InvalidOptionPropertyValueException {
    if (propertyName.equalsIgnoreCase("choices")) {
      String[] newChoices = propertyValue.split(",");
      for (String newChoice : newChoices) {
        choices.add(newChoice);
      }
    } else if (propertyName.equalsIgnoreCase("casesensitive")) {
      if (BooleanOption.validBooleanString(propertyValue)) {
        caseSensitive = Boolean.parseBoolean(propertyValue);
      } else {
        throw new InvalidOptionPropertyValueException("Invalid casesensitive, must be a boolean: " + propertyValue);
      }
    } else {
      super.setProperty(propertyName, propertyValue);
    }
  }

  @Override
  protected String getTypeString() {
    return "StringEnum";
  } 
  
  
}
