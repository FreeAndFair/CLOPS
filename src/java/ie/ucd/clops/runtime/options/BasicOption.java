/**
 * 
 */
package ie.ucd.clops.runtime.options;

import java.util.Collection;
import java.util.LinkedList;
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
  private String[] aliases;

  public BasicOption(String identifier, String prefixRegexp) {
    this.identifier = identifier;
    sanitizePrefix = true;
    dirty = true;
    
    this.prefix = prefixRegexp;
    this.suffix = SEP_STRING;
    this.aliases = new String[0];
  }

  /* (non-Javadoc)
   * @see ie.ucd.clops.runtime.options.IMatchable#getIdentifier()
   */
  public String getIdentifier() {
    return identifier;
  }

  /** Returns the value to which the option was set, or throws
   * {@code IllegalStateException} if the option was not set to
   * any value. */
  public T getValue() {
    if (!hasValue()) throw new IllegalStateException(
      "This option was not set. Either call is*Set() first or use getRaw*().(" + this + ")");
    return getRawValue();
  }

  public boolean hasValue() {
    return getRawValue() != null;
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
    return regexp.replaceAll("(^|([^\\\\]))\\(([^\\?])", "$1(?:$3");
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
    String p = sanitizePrefix ? "(" + sanitizePrefix(prefix) + ")" : prefix;
    pattern = Pattern.compile(p + suffix);
    dirty = false;
  }

  //Static for space/time efficiency (we don't need one per instance) 
  private static Collection<String> acceptedPropertyNames; 
  protected static Collection<String> getStaticAcceptedPropertyNames() {
    if (acceptedPropertyNames == null) {
      acceptedPropertyNames =  new LinkedList<String>();
      acceptedPropertyNames.add("default");
      acceptedPropertyNames.add("sanitizeprefix");
      acceptedPropertyNames.add("suffixregexp");
      acceptedPropertyNames.add("description");
      acceptedPropertyNames.add("aliases");
    }
    return acceptedPropertyNames;
  }
  
  @Override
  public Collection<String> getAcceptedPropertyNames() {
    return getStaticAcceptedPropertyNames();
  }
  
  public boolean acceptsProperty(String propertyName) {
    Collection<String> acceptedNames = getAcceptedPropertyNames();
    for (String acceptedName : acceptedNames) {
      if (propertyName.equalsIgnoreCase(acceptedName)) {
        return true;
      }
    }
    return false;
  }

  public void setProperty(String propertyName, String propertyValue) throws InvalidOptionPropertyValueException {
    if (propertyName.equals("default")) {
      try {
        this.setFromString(propertyValue);
      } catch (InvalidOptionValueException iove) {
        throw new InvalidOptionPropertyValueException("Invalid default value: " + iove.getMessage(), iove);
      }
    } else if (propertyName.equalsIgnoreCase("sanitizeprefix")) {
      sanitizePrefix = Options.parseBooleanProperty(propertyName, propertyValue);
    } else if (propertyName.equalsIgnoreCase("suffixregexp")) {
      setMatchingSuffix(propertyValue);
    } else if (propertyName.equalsIgnoreCase("description")) {
      this.description = propertyValue;
    } else if (propertyName.equalsIgnoreCase("aliases")) {
      this.aliases = propertyValue.split(",");
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

  @Override
  public String toString() {
    String r = getTypeString() + " Option: \"" + getIdentifier() + "\"";
    r += hasValue() ? "(=" + getValue() + ")" : "(not set)";
    return r;
  }

  public String getDescription() {
    return description;
  }

  public String getSuffix() {
      return suffix;
  }
  
  public String[] getAliases() {
    return aliases;
  }
}
