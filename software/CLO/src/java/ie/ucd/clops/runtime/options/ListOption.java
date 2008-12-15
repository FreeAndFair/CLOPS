package ie.ucd.clops.runtime.options;

import java.util.LinkedList;
import java.util.List;

/**
 * 
 * @author Fintan
 *
 * @param <T>
 */
public abstract class ListOption<T> extends OneArgumentOption<List<T>> {

  public static final String DEFAULT_SPLIT = ",";
  
  private List<T> value;
  private boolean allowMultiple;
  private String splittingString;
  
  public ListOption(String identifier, String prefix) {
    super(identifier, prefix);
    this.value = new LinkedList<T>();
    this.allowMultiple = true;
    this.splittingString = DEFAULT_SPLIT;
  }
  
  public List<T> getValue() {
    return value;
  }

  public void set(List<T> value) throws InvalidOptionValueException {
    this.value = value;
  }

  public void setFromString(String valueString) throws InvalidOptionValueException {
    if (allowMultiple) {
      String[] parts = valueString.split(splittingString);
      for (String part : parts) {
        T newValue = convertFromStringToListValue(part);
        value.add(newValue);
      }
    } else {
      T newValue = convertFromStringToListValue(valueString);
      value.add(newValue);
    }
  }

  /**
   * Convert from a String to a value to be stored in the list.
   * @param valueString the String to be converted.
   * @return an object of the appropriate type after conversion.
   * @throws InvalidOptionValueException if the String provided is invalid.
   */
  public abstract T convertFromStringToListValue(String valueString) throws InvalidOptionValueException;
  
  @Override
  public final List<T> convertStringToValue(String valueString) {
    //Should not be used
    assert false;
    return null;
  }

  public void unset() {
    this.value = new LinkedList<T>();
  }

  @Override
  public boolean acceptsProperty(String propertyName) {
    if (propertyName.equalsIgnoreCase("allowmultiple") ||  propertyName.equalsIgnoreCase("splitter")) {
      return true;
    } else {
      return super.acceptsProperty(propertyName);
    }
  }

  @Override
  public void setProperty(String propertyName, String propertyValue)
      throws InvalidOptionPropertyValueException {
    if (propertyName.equalsIgnoreCase("allowmultiple")) {
      if (BooleanOption.validBooleanString(propertyValue)) {
        allowMultiple = Boolean.parseBoolean(propertyValue);
      } else {
        throw new InvalidOptionPropertyValueException("Invalid allowmultiple, must be a boolean: " + propertyValue);
      } 
    } else if (propertyName.equalsIgnoreCase("splitter")) {
      splittingString = propertyValue;
    } else {
      super.setProperty(propertyName, propertyValue);
    }
  }

  
  
}
