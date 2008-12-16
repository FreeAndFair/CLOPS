package ie.ucd.clops.dsl;

import java.util.List;

/**
 * Represents information regarding a specific Option.
 * Contains information about the class representing the Option,
 * as well as the type of the value of the Option, and the method
 * used to extract the value. This is used by the code generator.
 *
 * A class representing a type of an option. 
 * To extend the DSL by a new option type, one provides an instance of this class.
 * The {@code OptionTypeFactory} is used to access these instances during the processing of the DSL.
 *
 * @author Fintan
 *
 */
public class OptionType {

  private static int count = 0; // counter used for unique identifiers of options types
  
  private final int type; // a unique identifier of this type
  private String typeDescriptionString;
  private String optionTypeClass;
  private String optionValueTypeClass;

  /** 
   * Initialize a new {@code OptionType}.
   *
   * @param typeDescriptionString  a textual description of the type
   * @param optionTypeClass a java class representing this option during option processing,
   *                     the class must implement the interface
   *                     {@link ie.ucd.clops.runtime.options.Option} instanciated with {@code optionValueTypeClass}
   * @param optionValueTypeClass a java class representing the value of this option type
   */  
  public OptionType(final String typeDescriptionString, String optionTypeClass, String optionValueTypeClass) {
    this.type = count++;
    this.typeDescriptionString = typeDescriptionString;
    this.optionTypeClass = optionTypeClass;
    this.optionValueTypeClass = optionValueTypeClass;
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

  public static String unifyRegexps(List<String> regexps) {
    if (regexps.size() == 0) {
      return "";
    } else {
      
      StringBuilder sb = new StringBuilder();
      for (String s : regexps) {
        sb.append("|(?:");
        sb.append(s);
        sb.append(")");
      }
      return sb.toString().substring(1);
    }
  }
  
}
