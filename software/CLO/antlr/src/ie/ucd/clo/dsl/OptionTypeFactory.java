package ie.ucd.clo.dsl;

import ie.ucd.clo.runtime.options.OptionType;

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
