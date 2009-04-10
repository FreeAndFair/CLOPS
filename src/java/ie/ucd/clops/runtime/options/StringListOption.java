package ie.ucd.clops.runtime.options;

import java.util.Collection;
import java.util.LinkedList;

/**
 * 
 * @author Fintan
 *
 */
public class StringListOption extends ListOption<String> {

  public StringListOption(String identifier, String prefix) {
    super(identifier, prefix);
  }

  @Override
  public String convertFromStringToListValue(String valueString)
      throws InvalidOptionValueException {
    return valueString;
  }

  @Override
  protected String getTypeString() {
    return "StringList";
  }
  
  @Override
  public Collection<String> getAcceptedPropertyNames() {
    return getStaticAcceptedPropertyNames();
  }
  
//Static for space/time efficiency (we don't need one per instance) 
  private static Collection<String> acceptedPropertyNames; 
  protected static Collection<String> getStaticAcceptedPropertyNames() {
    if (acceptedPropertyNames == null) {
      acceptedPropertyNames = new LinkedList<String>();  
      acceptedPropertyNames.addAll(StringOption.getStaticAcceptedPropertyNames());
      acceptedPropertyNames.addAll(ListOption.getStaticAcceptedPropertyNames());
    }
    return acceptedPropertyNames;
  }
}
