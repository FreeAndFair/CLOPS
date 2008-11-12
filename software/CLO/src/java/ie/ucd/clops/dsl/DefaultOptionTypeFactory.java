package ie.ucd.clops.dsl;

import ie.ucd.clops.dsl.parser.DSLParseException;


/**
 * @author Fintan
 *
 */
public class DefaultOptionTypeFactory extends OptionTypeFactory {

  /* (non-Javadoc)
   * @see ie.ucd.clo.dsl.OptionTypeFactory#getOptionType(java.lang.String)
   */
  public OptionType getOptionType(String optionType) throws DSLParseException {
    if (optionType.equalsIgnoreCase("bool") || optionType.equalsIgnoreCase("boolean")) {
      return OptionType.BOOLEAN;
    } else if (optionType.equalsIgnoreCase("string")) {
      return OptionType.STRING;
    } else if (optionType.equalsIgnoreCase("int") || optionType.equalsIgnoreCase("integer")) {
      return OptionType.INTEGER;
    } else if (optionType.equalsIgnoreCase("file")) {
      return OptionType.FILE; 
    } else if (optionType.equalsIgnoreCase("counted-boolean")) {
      return OptionType.COUNTED_BOOLEAN;
    } else if (optionType.equalsIgnoreCase("regexp-string")) {
      return OptionType.REG_EXP_STRING;
    } else if (optionType.equalsIgnoreCase("string-enum")) {
      return OptionType.STRING_ENUM;
//    } else if (optionType.equalsIgnoreCase("float")) {
//      return OptionType.FLOAT;
    } else {
      throw new DSLParseException("Unknown option type: " + optionType);
    }
  }

  public OptionType getDefaultOptionType() {
    return OptionType.BOOLEAN;
  }
  
  

}
