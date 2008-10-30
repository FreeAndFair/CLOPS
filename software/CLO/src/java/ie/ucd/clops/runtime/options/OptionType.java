package ie.ucd.clops.runtime.options;

/**
 *
 * @author fintan
 *
 */
public class OptionType {

  static final int BOOLEAN_TYPE = 0;
  static final int STRING_TYPE = 1;
  static final int INTEGER_TYPE = 2;
  static final int FLOAT_TYPE = 3;
  
  private int type;
  private String typeString;
  
  public OptionType(final int type, final String typeString) {
    this.type = type;
    this.typeString = typeString;
  }
  
  public int getType() {
    return type;
  }  
  
  public String toString() {
    return "Type: " + type + "(" + typeString + ")"; 
  }
  
  public String getTypeString() {
    return typeString;
  }
  
  public static final OptionType BOOLEAN = new OptionType(BOOLEAN_TYPE, "boolean");
  public static final OptionType STRING = new OptionType(STRING_TYPE, "string");
  public static final OptionType INTEGER = new OptionType(INTEGER_TYPE, "int");
  public static final OptionType FLOAT = new OptionType(FLOAT_TYPE, "float");
  
}
