package ie.ucd.clops.dsl;


/**
 * A factory for recognising Option types.
 * It provides a mapping from a String to an OptionType.
 * To add custom Option
 * 
 * @author Fintan
 *
 */
public abstract class OptionTypeFactory {
  
  private static OptionTypeFactory factory;
  
  /**
   * Get the OptionTypeFactory that is to be used.
   * @return the OptionTypeFactory to use.
   */
  public static OptionTypeFactory getOptionTypeFactory() {
    if (factory == null) {
      factory = new DefaultOptionTypeFactory();
    }
    return factory;
  }
  
  /**
   * Set the OptionTypeFactory that should be used.
   * This method is usually used to register a custom OptionTypeFactory
   * for use.
   * @param newFactory the factory to be used.
   */
  public static void setOptionTypeFactory(OptionTypeFactory newFactory) {
    factory = newFactory;
  }
  
  /**
   * 
   * @param optionType the string used to identify an OptionType
   * @return The option type for this name.
   */
  public abstract OptionType getOptionType(final String optionType) throws UnknownOptionTypeException;
  
  /**
   * Get the default OptionType for this factory.
   * @return the default OptionType for this factory.
   */
  public abstract OptionType getDefaultOptionType();
}
