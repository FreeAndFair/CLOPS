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
 * The {@code OptionTypeFactory} is used to access these instances 
 * during the processing of the DSL.
 *
 * @author Fintan
 *
 */
public class OptionType {
  
  /** counter used for unique identifiers of options types. */
  private static int count; 
  /** a unique identifier of this type. */
  private final int type;
  /** a textual description of the type. */
  private final String description;
  private String optionTypeClass;
  private String optionValueTypeClass;
  private String optionValueTypeParameterisation; 

  /** 
   * Initialize a new {@code OptionType}.
   *
   * @param typeDescription  a textual description of the type
   * @param typeClass a java class representing this option during option processing,
   *                     the class must implement the interface
   *                     {@link ie.ucd.clops.runtime.options.Option} 
   *                     instantiated with {@code optionValueTypeClass}
   * @param valueTypeClass a java type representing the return 
   * type value of this option type
   * @param valueTypeParameterisation a java class type that is 
   * the parameterisation of Option<?> for this option type
   */  
  public OptionType(final String typeDescription, 
                    final String typeClass, 
                    final String valueTypeClass, 
                    final String valueTypeParameterisation) {
    type = count++;
    description = typeDescription;
    optionTypeClass = typeClass;
    optionValueTypeClass = valueTypeClass;
    optionValueTypeParameterisation = valueTypeParameterisation;
  }

  public int getType() {
    return type;
  } 
  
  /** {@inheritDoc} */
  @Override
  public String toString() {
    return "Type: " + type + "(" + description + ")"; 
  }

  public String getTypeDescriptionString() {
    return description;
  }

  public String getOptionTypeClass() {
    return optionTypeClass;
  }

  public String getOptionValueTypeClass() {
    return optionValueTypeClass;
  }

  public String getOptionValueTypeParameterisation() {
    return optionValueTypeParameterisation;
  }

  /** {@inheritDoc} */
  @Override
  public boolean equals(final Object obj) {
    if (obj instanceof OptionType) {
      return getType() == ((OptionType)obj).getType();
    } 
    else {
      return false;
    }
  }

  /** {@inheritDoc} */
  @Override
  public int hashCode() {
    return getType(); 
  }

  public static String unifyRegexps(final List<String> regexps) {
    if (regexps.size() == 0) {
      return "";
    } 
    else {
      final StringBuilder sb = new StringBuilder();
      for (String s : regexps) {
        sb.append("|(?:");
        sb.append(s);
        sb.append(")");
      }
      return sb.toString().substring(1);
    }
  }

  public boolean implementsInterface(String interfaceName) {
    try {
      final Class< ? > clazz = Class.forName(optionTypeClass);
      final Class< ? > face = Class.forName(interfaceName);
      return face.isAssignableFrom(clazz);
    } 
    catch (ClassNotFoundException cnfe) {
      //TODO Log error!
      System.out.println("ClassNotFoundException: " + cnfe);
      cnfe.printStackTrace();
      return false;
    }
  }
}
