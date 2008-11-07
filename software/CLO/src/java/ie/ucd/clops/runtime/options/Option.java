package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.parser.ProcessingResult;

import java.util.Set;

/**
 * @author Mikolas Janota
 * @author Fintan
 *
 */
public interface Option extends IMatchable {
  
  /**
   * Match this option against the arguments starting at the given offset.
   * Returns a ProcessingResult indicating whether there was an error in processing
   * If there was an error an error message is contained in the ProcessingResult.
   * If the processing was successful, the ProcessingResult indicates how many arguments
   * were consumed.
   * @param args
   * @param offset
   * @return a ProcessingResult indicating the result of this processing.
   */
  ProcessingResult process(String[] args, int offset);
  
  /**
   * Does this Option have a value?
   * @return whether or not the option has a value set
   */
  boolean hasValue();
  
  /**
   * Get the value associated with this Option.
   * {@code hasValue() <=> getValue()!=null}.
   * @return the value associated with this Option.
   */
  Object getValue();
  
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
  void set(Object value) throws InvalidOptionValueException;

  /**
   * Sets the value of this Option from a string representation.
   * @param value a string representation of the value to set
   */
  void setFromString(String value) throws InvalidOptionValueException;
  
  void addAlias(String alias);

   /** Returns a set of aliases on which this option matches. */
   /*@non_null*/Set<String> getAliases();
  
   /** Sets the value of a property. 
    *  If {@code !acceptsProperty(propertyName)} then {@code InvalidOptionPropertyValueException} is thrown.
    * {@code InvalidOptionPropertyValueException} is also thrown when the value does not match the property type.
    */
  void setProperty(/*@non_null*/String propertyName, String propertyValue) throws InvalidOptionPropertyValueException;
  
   /** Determines whether this option supports the given property. */
   boolean acceptsProperty(/*@non_null*/String propertyName);
}
