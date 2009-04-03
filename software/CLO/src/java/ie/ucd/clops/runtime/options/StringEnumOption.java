package ie.ucd.clops.runtime.options;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Set;

/**
 * 
 * An option whose value is one of a given finite set of strings.
 * These string are given in the property "choices" and the value is a
 * comma-separated list of the individual values. The spaces are
 * preserved
 * @author Fintan
 *
 */
public class StringEnumOption extends StringOption {

  private final Set<String> choices;
  private boolean caseSensitive;
  
  public StringEnumOption(String identifier, String prefix) {
    super(identifier, prefix);
    choices = new HashSet<String>();
    caseSensitive = false;
  }

  public void addEnumChoice(String choice) {
    choices.add(choice);
  }

  @Override
  public void set(String value) throws InvalidOptionValueException {
    for (String choice : choices) {
      if ((caseSensitive && choice.equals(value)) || 
          choice.equalsIgnoreCase(value)) {
        super.set(value);
        return;
      }
    }
    throw new InvalidOptionValueException(value + " is not an allowed choice.");
  }

  //Static for space/time efficiency (we don't need one per instance) 
  private static Collection<String> acceptedPropertyNames; 
  protected static Collection<String> getStaticAcceptedPropertyNames() {
    if (acceptedPropertyNames == null) {
      acceptedPropertyNames = new LinkedList<String>();  
      acceptedPropertyNames.addAll(StringOption.getStaticAcceptedPropertyNames());
      acceptedPropertyNames.add("choices");
      acceptedPropertyNames.add("casesensitive");
    }
    return acceptedPropertyNames;
  }
  
  @Override
  public Collection<String> getAcceptedPropertyNames() {
    return getStaticAcceptedPropertyNames();
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
  protected String getTypeString() {
    return "StringEnum";
  } 
  
  
}
