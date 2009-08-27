package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.options.exception.InvalidOptionValueException;

import java.util.LinkedList;
import java.util.List;

/**
 * 
 * @author Fintan
 *
 */
public class CLOPSErrorOption extends StringListOption {

  public static final String ERROR_OPTION_ID = "CLOPSERROROPTION";
  public static String getErrorId() { return ERROR_OPTION_ID; }
  
  public CLOPSErrorOption() {
    super(ERROR_OPTION_ID, "");
  }
 
  @Override
  public Option<?> getMatchingOption(String argumentString, int index) {
    //Never matches!!
    return null;
  }

  @Override
  public void set(List<String> value) throws InvalidOptionValueException {
    internalGetList().addAll(value);
    this.isSet = true;
  }
  
  
  public static List<String> convertStringToStringList(String s) {
    List<String> list = new LinkedList<String>();
    list.add(s);
    return list;
  }
}
