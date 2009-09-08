package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.options.exception.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.options.exception.InvalidOptionValueException;
import ie.ucd.clops.runtime.parser.ProcessingResult;

import java.util.Collection;

/**
 * This interface describes information about the option needed during option parsing.
 *
 * @author Mikolas Janota
 * @author Fintan
 *
 */
public interface Option<T> extends IMatchable {

  /**
   * Does this Option have a value?
   * @return whether or not the option has a value set
   */
  /*@pure*/boolean hasValue();

  /**
   * Get the value associated with this Option.
   * @return the value associated with this Option.
   * @throws IllegalStateException if this option wasn't set
   */
  /*@pure*/T getValue();

  /**
   * Get the value associated with this Option.
   * {@code hasValue() <=> getRawValue()!=null}.
   * @return the value associated with this Option.
   */
  /*@pure*/T getRawValue();

  /**
   * Unset this Option.
   * after this call, {@code !hasValue()}
   */
  void unset();

  /**
   * Sets the value of this Option.
   * after this call, {@code hasValue()}
   * 
   * TODO - should this method throw an exception or return something when 
   * an invalid value is provided?
   * 
   * @param value
   */
  void set(T value) throws InvalidOptionValueException;

  /**
   * Sets the value of this Option from a string representation.
   * @param value a string representation of the value to set
   */
  void setFromString(String optionAlias, String value) throws InvalidOptionValueException;

  /**
   * Convert from a String to a value of this option's type.
   * @param valueString the String to be converted.
   * @return an object of the appropriate type after conversion.
   * @throws InvalidOptionValueException if the String provided is invalid.
   */
  T convertStringToValue(String valueString) throws InvalidOptionValueException;

  /** Sets the value of a property. 
   *  If {@code !acceptsProperty(propertyName)} then {@code InvalidOptionPropertyValueException} is thrown.
   * {@code InvalidOptionPropertyValueException} is also thrown when the value does not match the property type.
   */
  void setProperty(/*@non_null*/String propertyName, String propertyValue) throws InvalidOptionPropertyValueException;
  
  Collection<String> getAcceptedPropertyNames();

  /** Determines whether this option supports the given property. */
  /*@pure*/boolean acceptsProperty(/*@non_null*/String propertyName);

  void setMatchingPrefix(String regexp);

  int getMatchLength();

  /** Returns the string that should determine the value of the option,
   * according to the last successful match operation. */
  String getMatchingValueString();
  
  String[] getAliases();
  
  String getDescription();
}
