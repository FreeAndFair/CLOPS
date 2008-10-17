package ie.ucd.clops.dsl;

import ie.ucd.clops.dsl.structs.OptionType;

/**
 * 
 * @author fintan
 *
 */
public interface OptionTypeFactory {
  
  /**
   * 
   * @param optionType
   * @return The option type for this name.
   */
  OptionType getOptionType(final String optionType) throws DSLParseException;
  
}
