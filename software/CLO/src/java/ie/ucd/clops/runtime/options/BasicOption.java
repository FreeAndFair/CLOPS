/**
 * 
 */
package ie.ucd.clops.runtime.options;

import java.util.LinkedList;
import java.util.List;
import java.util.regex.MatchResult;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * @author Fintan
 *
 */
public abstract class BasicOption<T> implements Option<T> {

  private final String identifier;

  private boolean sanitizePrefix;
  private boolean dirty;
  
  private String prefix;
  private String suffix;
  private Pattern pattern;
  
  protected MatchResult match;
  
  private String lastArgumentString;
  private Matcher matcher;
  
  private String description;

  public BasicOption(String identifier, String prefixRegexp) {
    this.identifier = identifier;
    sanitizePrefix = true;
    dirty = true;
    
    this.prefix = prefixRegexp;
    this.suffix = SEP_STRING;
  }

  /* (non-Javadoc)
   * @see ie.ucd.clops.runtime.options.IMatchable#getIdentifier()
   */
  public String getIdentifier() {
    return identifier;
  }

  public boolean hasValue() {
    return getValue() != null;
  }
  
  public int getMatchLength() { 
    return match.end() - match.start();
  }

  @Override
  public final void setMatchingPrefix(String regexp) {
    prefix = regexp;
    dirty = true;
  }
  
  public static String sanitizePrefix(String regexp) {
    return '(' + regexp.replaceAll("(^|([^\\\\]))\\(([^\\?])", "$1(?:$3") + ')';
  }

  public Option<?> getMatchingOption(String argumentString, int index) {
    if (dirty) {
      updatePattern();
    }
    
    if (argumentString != lastArgumentString) {
      matcher = pattern.matcher(argumentString);
      lastArgumentString = argumentString;
    } 
    matcher.region(index, argumentString.length());
    boolean matched = matcher.lookingAt();
    if (matched) {
      match = matcher.toMatchResult();
      return this;
    } else {
      return null;
    }
  }

  @Override
  public void setFromString(String valueString) throws InvalidOptionValueException {
    set(convertStringToValue(valueString));
  }

  protected final void setMatchingSuffix(String regexp) {
    suffix = regexp;
    dirty = true;
  }
  
  private void updatePattern() {
    String p = sanitizePrefix ? sanitizePrefix(prefix) : prefix;
    pattern = Pattern.compile(p + suffix);
    dirty = false;
  }

  public boolean acceptsProperty(String propertyName) {
    return propertyName.equalsIgnoreCase("default") || propertyName.equalsIgnoreCase("sanitizeprefix") ||
           propertyName.equalsIgnoreCase("suffixregexp") || propertyName.equalsIgnoreCase("description");
  }

  public void setProperty(String propertyName, String propertyValue) throws InvalidOptionPropertyValueException {
    if (propertyName.equals("default")) {
      try {
        this.setFromString(propertyValue);
      } catch (InvalidOptionValueException iove) {
        throw new InvalidOptionPropertyValueException("Invalid default value: " + iove.getMessage(), iove);
      }
    } else if (propertyName.equalsIgnoreCase("sanitizeprefix")) {
      if (BooleanOption.validBooleanString(propertyName)) {
        sanitizePrefix = Boolean.parseBoolean(propertyValue);
      } else {
        throw new InvalidOptionPropertyValueException("Invalid boolean value: " + propertyValue);
      }
    } else if (propertyName.equalsIgnoreCase("suffixregexp")) {
      setMatchingSuffix(propertyValue);
    } else if (propertyName.equalsIgnoreCase("description")) {
      this.description = propertyValue;
    } else {
      throw new InvalidOptionPropertyValueException("Unknown property " + propertyName);
    }
  }

  @Override
  public boolean equals(Object obj) {
    if (obj instanceof BasicOption) {
      this.getIdentifier().equals(((BasicOption<?>)obj).getIdentifier());
    } else {
      return false;
    }
    return super.equals(obj);
  }

  @Override
  public int hashCode() {
    return getIdentifier().hashCode();
  }

  protected abstract String getTypeString();

  private final static Pattern ALIAS_PATTERN = Pattern.compile("\\(\\?\\:(.+)\\)");
  //Warning, currently a VERY naive implementation
  public List<String> getAliases() {
    String[] parts = prefix.split("\\|");
    List<String> aliases = new LinkedList<String>();
    for (String part : parts) {
      if (part.charAt(0) == '(' && part.charAt(1) == '?') {
        part = part.substring(3,part.length()-1);
      }
      aliases.add(part);
    }
    return aliases;
  }
  
  @Override
  public String toString() {
    String r = getTypeString() + " Option: \"" + getIdentifier() + "\"";
    r += hasValue() ? "(=" + getValue() + ")" : "(not set)";
    return r;
  }
  
}
