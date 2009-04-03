package ie.ucd.clops.dsl;

import java.util.HashMap;
import java.util.Map;



/**
 * A default version of the  factory for option types
 * ({@link ie.ucd.clops.dsl.OptionType}) that is used
 * during the processing of the DSL. One should extend this
 * class to provide for new option types.
 *
 * @author Fintan
 *
 */
public class DefaultOptionTypeFactory extends OptionTypeFactory {

  public static final OptionType BOOLEAN = new OptionType("boolean", "ie.ucd.clops.runtime.options.BooleanOption", "boolean", "Boolean");
  public static final OptionType COUNTED_BOOLEAN = new OptionType("counted-boolean", "ie.ucd.clops.runtime.options.CountedBooleanOption", "int", "Integer");
  public static final OptionType STRING = new OptionType("string", "ie.ucd.clops.runtime.options.StringOption", "String", "String");
  public static final OptionType INTEGER = new OptionType("int", "ie.ucd.clops.runtime.options.IntegerOption", "int", "Integer");
  public static final OptionType FLOAT = new OptionType("float", "ie.ucd.clops.runtime.options.FloatOption", "float", "Float");
  public static final OptionType FILE = new OptionType("file", "ie.ucd.clops.runtime.options.FileOption", "java.io.File", "java.io.File");
  public static final OptionType STRING_REGEXP = new OptionType("string-regexp", "ie.ucd.clops.runtime.options.RegularExpressionStringOption", "String", "String");
  public static final OptionType STRING_ENUM = new OptionType("string-enum", "ie.ucd.clops.runtime.options.StringEnumOption", "String", "String");
  public static final OptionType STRING_LIST = new OptionType("string-list", "ie.ucd.clops.runtime.options.StringListOption", "java.util.List<String>", "java.util.List<String>");
  public static final OptionType FILE_LIST = new OptionType("file-list", "ie.ucd.clops.runtime.options.FileListOption", "java.util.List<java.io.File>", "java.util.List<java.io.File>");
  
  private final Map<String,OptionType> optionTypeMap;
  
  public DefaultOptionTypeFactory() {
    optionTypeMap = new HashMap<String,OptionType>();
    initialise();
  }
  
  public void registerOptionType(String name, OptionType type) {
    optionTypeMap.put(name, type);
  }
  
  private static final OptionType[] BUILT_INS = {BOOLEAN, COUNTED_BOOLEAN, STRING, INTEGER, FLOAT, FILE, STRING_ENUM, STRING_REGEXP, STRING_LIST, FILE_LIST};
  private void initialise() {
    for (OptionType type : BUILT_INS) {
      registerOptionType(type.getTypeDescriptionString(), type);
    }
    //Some additional mappings:
    registerOptionType("bool", BOOLEAN);
    registerOptionType("integer", INTEGER);
  }
  
  /* (non-Javadoc)
   * @see ie.ucd.clo.dsl.OptionTypeFactory#getOptionType(java.lang.String)
   */
  public OptionType getOptionType(String optionType) throws UnknownOptionTypeException {
    OptionType type = optionTypeMap.get(optionType);
    if (type != null) {
      return type;
    } else {
      throw new UnknownOptionTypeException("Unknown option type: " + optionType);
    }
  }

  public OptionType getDefaultOptionType() {
    return DefaultOptionTypeFactory.BOOLEAN;
  }
}
