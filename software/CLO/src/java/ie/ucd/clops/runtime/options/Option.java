package ie.ucd.clops.runtime.options;

import java.util.Set;

import ie.ucd.clops.runtime.parser.ProcessingResult;

/**
 * @author Mikolas Janota
 * @author Fintan
 *
 */
public interface Option extends IMatchable {
  
  /**
   * Get the type of this Option.
   * @return The OptionType associated with this Option.
   */
  OptionType getType();
  
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
   * @return whether or not the option has a value set.
   */
  boolean hasValue();
  
  /**
   * Get the value associated with this Option.
   * hasValue() <=> getValue()!=null.
   * @return the value associated with this Option.
   */
  Object getValue();
  
  /**
   * Unset this Option.
   * after this call, hasValue()==false
   */
  void unset();
  
  /**
   * Sets the value of this Option.
   * after this call, hasValue()==true
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
  
  Set<String> getAliases();
  
}
