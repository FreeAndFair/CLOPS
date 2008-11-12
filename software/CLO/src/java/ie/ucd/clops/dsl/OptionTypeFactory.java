package ie.ucd.clops.dsl;

import ie.ucd.clops.dsl.parser.DSLParseException;


/**
 * 
 * @author Fintan
 *
 */
public abstract class OptionTypeFactory {
  
  private static OptionTypeFactory factory;
  
  public static OptionTypeFactory getOptionTypeFactory() {
    if (factory == null) {
      factory = new DefaultOptionTypeFactory();
    }
    return factory;
  }
  
  public static void setOptionTypeFactory(OptionTypeFactory newFactory) {
    factory = newFactory;
  }
  
  /**
   * 
   * @param optionType
   * @return The option type for this name.
   */
  public abstract OptionType getOptionType(final String optionType) throws DSLParseException;
  
  public abstract OptionType getDefaultOptionType();
}
