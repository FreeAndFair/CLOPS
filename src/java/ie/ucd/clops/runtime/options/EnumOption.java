package ie.ucd.clops.runtime.options;

import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.Map;
import java.util.Set;

import ie.ucd.clops.runtime.options.exception.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.options.exception.InvalidOptionValueException;
import ie.ucd.clops.util.StringUtil;

/**
 * 
 * An option whose value is one of a given finite set of strings.
 * These string are given in the property "choices" and the value is a
 * comma-separated list of the individual values. The spaces are
 * preserved
 * @author Fintan
 *
 */
public class EnumOption extends StringOption implements IEnumOption {

  private final EnumPart enumPart;

  public EnumOption(String identifier, String prefix) {
    super(identifier, prefix);
    enumPart = new EnumPart();
  }

  @Override
  public void set(String value) throws InvalidOptionValueException {
    if (enumPart.isValidValue(value)) {
      super.set(value);
    } else {
      throw new InvalidOptionValueException(value + " is not an allowed choice.");
    } 
  }

  //Static for space/time efficiency (we don't need one per instance) 
  private static Collection<String> acceptedPropertyNames; 
  protected static Collection<String> getStaticAcceptedPropertyNames() {
    if (acceptedPropertyNames == null) {
      acceptedPropertyNames = new LinkedList<String>();  
      acceptedPropertyNames.addAll(StringOption.getStaticAcceptedPropertyNames());
      acceptedPropertyNames.addAll(EnumPart.getStaticAcceptedPropertyNames());
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
    if (!enumPart.setProperty(propertyName, propertyValue)) {
      super.setProperty(propertyName, propertyValue);
    }
  }

  public EnumPart getEnumPart() {
    return enumPart;
  }

  @Override
  protected String getTypeString() {
    return "StringEnum";
  } 

  public static class EnumPart {

    private final Set<String> choices;
    private boolean caseSensitive;

    public EnumPart() {
      choices = new HashSet<String>();
      caseSensitive = false;
    }

    public void addChoice(String choice) {
      choices.add(choice);
    }

    public boolean isValidValue(String value) {
      return isValidValue(value, choices, caseSensitive);
    }

    public static boolean isValidValue(String value, Set<String> choices, boolean caseSensitive) {
      for (String choice : choices) {
        if ((caseSensitive && choice.equals(value)) || 
            choice.equalsIgnoreCase(value)) {
          return true;
        }
      }
      return false;
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

    public Collection<String> getAcceptedPropertyNames() {
      return getStaticAcceptedPropertyNames();
    }

    public boolean setProperty(String propertyName, String propertyValue)
    throws InvalidOptionPropertyValueException {
      if (propertyName.equalsIgnoreCase("choices")) {
        // TODO(rgrig): this should by in sync with StringUtil.parseChoice
        for (String c : propertyValue.split(",")) {
          int i = c.indexOf("(");
          if (i != -1) c = c.substring(0, i);
          choices.add(c);
        }
        return true;
      } else if (propertyName.equalsIgnoreCase("casesensitive")) {
        caseSensitive = Options.parseBooleanProperty(propertyName, propertyValue);
        return true;
      } else {
        return false;
      }
    }
  }

}


