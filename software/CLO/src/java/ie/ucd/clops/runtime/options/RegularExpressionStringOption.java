package ie.ucd.clops.runtime.options;

import java.util.Set;
import java.util.regex.Pattern;
import java.util.regex.PatternSyntaxException;

/**
 * 
 * @author Fintan
 *
 */
public class RegularExpressionStringOption extends StringOption {

  private static final String DEFAULT_REG_EXP = ".*";
  
  private String value;
  private Pattern pattern;
  
  public RegularExpressionStringOption(String identifier, Set<String> aliases) {
    super(identifier, aliases);
    this.pattern = Pattern.compile(DEFAULT_REG_EXP);
  }

  public RegularExpressionStringOption(String identifier) {
    super(identifier);
    this.pattern = Pattern.compile(DEFAULT_REG_EXP);
  }

  @Override
  public void set(Object value) throws InvalidOptionValueException {
    if (value instanceof String) {
      String input = (String)value;
      if (!pattern.matcher(input).matches()) {
        throw new InvalidOptionValueException("");
      } else {
        this.value = input;
      }
    } else {
      throw new InvalidOptionValueException(value + " is not a String.");
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
