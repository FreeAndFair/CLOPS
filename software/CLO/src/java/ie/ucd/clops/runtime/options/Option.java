package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.parser.ProcessingResult;

/**
 * @author Mikolas Janota
 * @author Fintan
 *
 */
public interface Option extends IMatchable {

  /**
   * Get the type of this Option.
   * @return
   */
  OptionType getType();
  
  /**
   * Match this option against the arguments starting at the given offset.
   * Returns a MatchResult indicating a match, lack of match or an error 
   * that occurred during matching.
   * @param args
   * @param offset
   * @return
   */
  ProcessingResult process(String[] args, int offset);
  
  /**
   * Does this Option have a value?
   * @return
   */
  boolean hasValue();
  
  /**
   * Get the value associated with this Option.
   * hasValue() <=> getValue()!=null.
   * @return
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
  void set(Object value);
  
}
