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
   * @return
   */
  OptionType getOptionType(final String optionType) throws DSLParseException;
  
}
