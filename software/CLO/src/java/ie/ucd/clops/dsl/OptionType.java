package ie.ucd.clops.dsl;

/**
 *
 * @author Fintan
 *
 */
public class OptionType {

  private static int count = 0;
  
  private int type;
  private String typeDescriptionString;
  private String optionTypeClass;
  private String optionValueTypeClass;
  private String optionValueGetterMethodName;
  
  public OptionType(final String typeDescriptionString, String optionTypeClass, String optionValueTypeClass, String optionValueGetterMethodName) {
    this.type = count++;
    this.typeDescriptionString = typeDescriptionString;
    this.optionTypeClass = optionTypeClass;
    this.optionValueTypeClass = optionValueTypeClass;
    this.optionValueGetterMethodName = optionValueGetterMethodName;
  }
  
  public int getType() {
    return type;
  }  
  
  public String toString() {
    return "Type: " + type + "(" + typeDescriptionString + ")"; 
  }
  
  public String getTypeDescriptionString() {
    return typeDescriptionString;
  }
  
  public String getOptionTypeClass() {
    return optionTypeClass;
  }

  public String getOptionValueTypeClass() {
    return optionValueTypeClass;
  }

  public String getOptionValueGetterMethodName() {
    return optionValueGetterMethodName;
  }

  @Override
  public boolean equals(Object obj) {
    if (obj instanceof OptionType) {
      return getType() == ((OptionType)obj).getType();
    } else {
      return false;
    }
  }

  @Override
  public int hashCode() {
    return getType(); 
  }

  public static final OptionType BOOLEAN = new OptionType("boolean", "ie.ucd.clops.runtime.options.BooleanOption", "boolean", "getBooleanValue");
  public static final OptionType COUNTED_BOOLEAN = new OptionType("counted-boolean", "ie.ucd.clops.runtime.options.CountedBooleanOption", "int", "getCount");
  public static final OptionType STRING = new OptionType("string", "ie.ucd.clops.runtime.options.StringOption", "String", "getStringValue");
  public static final OptionType INTEGER = new OptionType("int", "ie.ucd.clops.runtime.options.IntegerOption", "int", "getIntegerValue");
  public static final OptionType FILE = new OptionType("file", "ie.ucd.clops.runtime.options.FileOption", "File", "getFileValue");
  //public static final OptionType FLOAT = new OptionType("float", "ie.ucd.clops.runtime.options.FloatOption", "float", "getFloatValue");
  
}
