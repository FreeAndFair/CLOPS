package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.options.exception.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.options.exception.InvalidOptionValueException;

import java.util.Collection;
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

  /** A variable indicating if this list option has been set. */
  protected boolean isSet;
  
  private List<T> value;
  private boolean allowMultiple;
  protected String splittingString;

  public ListOption(String identifier, String prefix) {
    super(identifier, prefix);
    this.value = new LinkedList<T>();
    this.allowMultiple = true;
    this.splittingString = DEFAULT_SPLIT;
    this.isSet = false;
    
    try {
      super.setProperty(ARGUMENTNAME, "<args>");
    } catch (InvalidOptionPropertyValueException e) {};
  }

  protected List<T> internalGetList() {
    return value;
  }
  
  public List<T> getRawValue() {
    return value;
  }

  public void set(List<T> value) throws InvalidOptionValueException {
    this.value = value;
    this.isSet = true;
  }

  public void setFromString(String optionAlias, String valueString) throws InvalidOptionValueException {
    valueString = convertToDefaultIfNecessary(optionAlias, valueString);
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
    isSet = true;
  }

  /**
   * Convert from a String to a value to be stored in the list.
   * @param valueString the String to be converted.
   * @return an object of the appropriate type after conversion.
   * @throws InvalidOptionValueException if the String provided is invalid.
   */
  public abstract T convertFromStringToListValue(String valueString) throws InvalidOptionValueException;

  /**
   * This should never be used, but is required by the interface of Option.
   */
  public final List<T> convertStringToValue(String valueString) {
    //Should not be used
    assert false;
    return null;
  }

  public void unset() {
    this.value = new LinkedList<T>();
    this.isSet = false;
  }

  @Override
  public boolean hasValue() {
    return isSet;
  }

  //Static for space/time efficiency (we don't need one per instance) 
  private static Collection<String> acceptedPropertyNames; 
  protected static Collection<String> getStaticAcceptedPropertyNames() {
    if (acceptedPropertyNames == null) {
      acceptedPropertyNames = new LinkedList<String>();  
      acceptedPropertyNames.addAll(OneArgumentOption.getStaticAcceptedPropertyNames());
      acceptedPropertyNames.add("allowmultiple");
      acceptedPropertyNames.add("splitter");
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
    if (propertyName.equalsIgnoreCase("allowmultiple")) {
      allowMultiple = Options.parseBooleanProperty(propertyName, propertyValue);
    } else if (propertyName.equalsIgnoreCase("splitter")) {
      splittingString = propertyValue;
    } else {
      super.setProperty(propertyName, propertyValue);
    }
  }  

}
