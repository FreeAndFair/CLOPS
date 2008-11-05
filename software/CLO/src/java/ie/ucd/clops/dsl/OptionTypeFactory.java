package ie.ucd.clops.dsl;


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
  
  OptionType getDefaultOptionType();
}
