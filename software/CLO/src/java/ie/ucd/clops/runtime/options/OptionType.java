package ie.ucd.clops.runtime.options;

/**
 *
 * @author fintan
 *
 */
public class OptionType {

  private static int count = 0;
  
  private int type;
  private String typeString;
  
  public OptionType(final String typeString, String typeClass) {
    this.type = count++;
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

  public static final OptionType BOOLEAN = new OptionType("boolean", "ie.ucd.clops.runtime.options.BooleanOption");
  public static final OptionType STRING = new OptionType("string", "ie.ucd.clops.runtime.options.StringOption");
  public static final OptionType INTEGER = new OptionType("int", "ie.ucd.clops.runtime.options.IntegerOption");
  //public static final OptionType FLOAT = new OptionType("float", "ie.ucd.clops.runtime.options.FloatOption");
  
}
