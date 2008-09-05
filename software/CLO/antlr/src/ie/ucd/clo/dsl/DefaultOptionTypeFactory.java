package ie.ucd.clo.dsl;

import java.awt.geom.Line2D;

import ie.ucd.clo.dsl.structs.OptionType;

/**
 * @author fintan
 *
 */
public class DefaultOptionTypeFactory implements OptionTypeFactory {

  /* (non-Javadoc)
   * @see ie.ucd.clo.dsl.OptionTypeFactory#getOptionType(java.lang.String)
   */
  @Override
  public OptionType getOptionType(String optionType) throws DSLParseException {
    if (optionType.equalsIgnoreCase("bool") || optionType.equalsIgnoreCase("boolean")) {
      return OptionType.BOOLEAN;
    } else if (optionType.equalsIgnoreCase("string")) {
      return OptionType.STRING;
    } else if (optionType.equalsIgnoreCase("int") || optionType.equalsIgnoreCase("integer")) {
      return OptionType.INTEGER;
    } else if (optionType.equalsIgnoreCase("float")) {
      return OptionType.FLOAT;
    } else {
      throw new DSLParseException("Unknown option type: " + optionType);
    }
  }

}
