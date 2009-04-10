package ie.ucd.clops.runtime.options;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Set;

public class EnumListOption extends StringListOption implements IEnumListOption {

  private final Set<String> choices;
  private boolean caseSensitive;

  public EnumListOption(String identifier, String prefix) {
    super(identifier, prefix);
    choices = new HashSet<String>();
    caseSensitive = false;
  }

  @Override
  public void setFromString(String valueString) throws InvalidOptionValueException {
    if (isValidValue(valueString)) {
      super.setFromString(valueString);
    } else {
      throw new InvalidOptionValueException(valueString + " is not an allowed choice.");
    }    
  }

  @Override
  public void set(List<String> value) throws InvalidOptionValueException {
    List<String> invalidValues = new LinkedList<String>();
    for (String v : value) {
      if (!isValidValue(v)) {
        invalidValues.add(v);
      }
    }
    if (invalidValues.size() == 0) {
      super.set(value);
    } else {
      if (invalidValues.size() == 1) {
        throw new InvalidOptionValueException(invalidValues.get(0) + " is not an valid choice.");
      } else {
        throw new InvalidOptionValueException(invalidValues + " are not valid choices.");
      }
    }
  }

  public boolean isValidValue(String value) {
    return EnumOption.isValidValue(value, choices, caseSensitive);
  }

  @Override
  protected String getTypeString() {
    return "EnumList";
  }

  //Static for space/time efficiency (we don't need one per instance) 
  private static Collection<String> acceptedPropertyNames; 
  protected static Collection<String> getStaticAcceptedPropertyNames() {
    if (acceptedPropertyNames == null) {
      acceptedPropertyNames = new LinkedList<String>();  
      acceptedPropertyNames.addAll(StringListOption.getStaticAcceptedPropertyNames());
      acceptedPropertyNames.add("choices");
      acceptedPropertyNames.add("casesensitive");
    }
    return acceptedPropertyNames;
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
      caseSensitive = Options.parseBooleanProperty(propertyName, propertyValue);
    } else {
      super.setProperty(propertyName, propertyValue);
    }
  }

  @Override
  public Collection<String> getAcceptedPropertyNames() {
    return getStaticAcceptedPropertyNames();
  }

}
