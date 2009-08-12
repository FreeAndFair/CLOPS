package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.options.exception.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.options.exception.InvalidOptionValueException;

import java.util.Collection;
import java.util.LinkedList;
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
  
    //  private String value;
  private Pattern pattern;
  
  public RegularExpressionStringOption(String identifier, String prefix) {
    super(identifier, prefix);
    this.pattern = Pattern.compile(DEFAULT_REG_EXP);
  }

  @Override
  public void set(String value) throws InvalidOptionValueException {
    if (!pattern.matcher(value).matches()) {
      throw new InvalidOptionValueException(value + " doesn't match on " + pattern.pattern());
    } else {
      super.set(value);
    }
  }

  //Static for space/time efficiency (we don't need one per instance) 
  private static Collection<String> acceptedPropertyNames; 
  protected static Collection<String> getStaticAcceptedPropertyNames() {
    if (acceptedPropertyNames == null) {
      acceptedPropertyNames = new LinkedList<String>();  
      acceptedPropertyNames.addAll(StringOption.getStaticAcceptedPropertyNames());
      acceptedPropertyNames.add("regexp");
    }
    return acceptedPropertyNames;
  }
  
  @Override
  public Collection<String> getAcceptedPropertyNames() {
    return getStaticAcceptedPropertyNames();
  }
  
  @Override
  public void setProperty(String propertyName, String propertyValue)
      throws InvalidOptionPropertyValueException {
    if (propertyName.equalsIgnoreCase("regexp")) {
      try {
        pattern = Pattern.compile(propertyValue);
      } catch (PatternSyntaxException pse) {
        throw new InvalidOptionPropertyValueException("Invalid value for regexp: " + propertyValue, pse);
      }
    } else {
      super.setProperty(propertyName, propertyValue);
    }
  }

  @Override
  protected String getTypeString() {
    return "RegularExpressionString";
  }
  
  
  
}
