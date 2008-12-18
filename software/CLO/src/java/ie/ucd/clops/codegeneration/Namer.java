package ie.ucd.clops.codegeneration;

import ie.ucd.clops.dsl.structs.OptionDescription;
import ie.ucd.clops.dsl.structs.OptionGroupDescription;

/**
 * 
 * @author Fintan
 *
 */
public class Namer {

  public static String getIsSetMethodName(OptionDescription od) {
    return "is" + od.getIdentifier() + "Set";
  }
  
  public static String getGetValueMethodName(OptionDescription od) {
    return "get" + od.getIdentifier();
  }
  
  public static String getGetOptionMethodName(OptionDescription od) {
    return "get" + od.getIdentifier() + "Option";
  }
  
  public static String getOptionInstanceName(OptionDescription od) {
    return od.getIdentifier() + "OG";
  }
  
  public static String getOptionGroupInstanceName(OptionGroupDescription ogd) {
    return ogd.getIdentifier() + "OG";
  }
  
  public static String getOptionGroupChildInstanceName(String name) {
    return name + "OG";
  }
  
}
