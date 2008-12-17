package ie.ucd.clops.runtime.options;

import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;

/**
 * 
 * An option type whose value is  regular expression. 
 * The expression is determined by the property "regexp".
 * The expression has the same syntax as a java regular expression.
 * @author Fintan
 *
 */
public class RegularExpressionStringOption extends StringOption {

  private static final String DEFAULT_REG_EXP = ".*";
  
  private String value;
  private Pattern pattern;
  
  public RegularExpressionStringOption(String identifier, String prefix) {
    super(identifier, prefix);
    this.pattern = Pattern.compile(DEFAULT_REG_EXP);
  }

  @Override
  public void set(String value) throws InvalidOptionValueException {
    String input = (String)value;
    if (!pattern.matcher(input).matches()) {
      throw new InvalidOptionValueException("");
    } else {
      this.value = input;
    }
  }

  @Override
  public boolean acceptsProperty(String propertyName) {
    if (propertyName.equalsIgnoreCase("regexp")) {
      return true;
    } else {
      return super.acceptsProperty(propertyName);
    }
  }
  
  @Override
  public void setProperty(String propertyName, String propertyValue)
      throws InvalidOptionPropertyValueException {
    if (propertyName.equalsIgnoreCase("regexp")) {
      try {
        pattern = Pattern.compile(propertyValue);
      } catch (PatternSyntaxException pse) {
        throw new InvalidOptionPropertyValueException("Invalid value for regexp: " + propertyValue);
      }
    } else {
      super.setProperty(propertyName, propertyValue);
    }
  }

  public String getStringValue() {
    return value;
  }

  @Override
  protected String getTypeString() {
    return "RegularExpressionString";
  }
  
  
  
}
