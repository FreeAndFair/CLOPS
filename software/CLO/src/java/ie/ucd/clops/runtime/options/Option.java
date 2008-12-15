package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.parser.ProcessingResult;

/**
 * This interface describes information about the option needed during option parsing.
 *
 * @author Mikolas Janota
 * @author Fintan
 *
 */
public interface Option<T> extends IMatchable {
  
  /**
   * Match this option against the arguments starting at the given offset.
   * Returns a {@code ProcessingResult} indicating whether there was an error in the processing.
   * If there was an error, an error message is contained in the ProcessingResult.
   * If the processing was successful, the {@code ProcessingResult} indicates how many arguments
   * were consumed.
   * @return a {@code ProcessingResult} indicating the result of this processing
   */
   //@ requires 0 <= offset && offset < args.length;
   ProcessingResult process();
  
  /**
   * Does this Option have a value?
   * @return whether or not the option has a value set
   */
   /*@pure*/boolean hasValue();
  
  /**
   * Get the value associated with this Option.
   * {@code hasValue() <=> getValue()!=null}.
   * @return the value associated with this Option.
   */
   /*@pure*/T getValue();
  
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
  void setFromString(String value) throws InvalidOptionValueException;
  
  T convertStringToValue(String valueString) throws InvalidOptionValueException;
  
   /** Sets the value of a property. 
    *  If {@code !acceptsProperty(propertyName)} then {@code InvalidOptionPropertyValueException} is thrown.
    * {@code InvalidOptionPropertyValueException} is also thrown when the value does not match the property type.
    */
  void setProperty(/*@non_null*/String propertyName, String propertyValue) throws InvalidOptionPropertyValueException;
  
   /** Determines whether this option supports the given property. */
   /*@pure*/boolean acceptsProperty(/*@non_null*/String propertyName);
   
   void setMatchingPrefix(String regexp);
   
   int getMatchLength();
   
}
