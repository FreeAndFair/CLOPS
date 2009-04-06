package ie.ucd.clops.runtime.options;

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

  
  
}
