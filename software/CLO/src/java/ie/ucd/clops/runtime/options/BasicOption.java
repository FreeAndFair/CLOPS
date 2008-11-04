/**
 * 
 */
package ie.ucd.clops.runtime.options;

import java.util.HashSet;
import java.util.Set;

/**
 * @author Fintan
 *
 */
public abstract class BasicOption implements Option {

  private final Set<String> aliases;
  private final String identifier;
  
  public BasicOption(String identifier, final Set<String> aliases) {
    this.identifier = identifier;
    this.aliases = aliases;
  }
  
  public BasicOption(String identifier) {
    this(identifier, new HashSet<String>());
  }
  
  public Set<String> getAliases() {
    return aliases;
  }
  
  public void addAlias(String alias) {
    aliases.add(alias);
  }
  
  /* (non-Javadoc)
   * @see ie.ucd.clops.runtime.options.IMatchable#getIdentifier()
   */
  public String getIdentifier() {
    return identifier;
  }

  public Option getMatchingOption(String argument) {
    String matchedAlias = getMatchingAlias(argument);
    return matchedAlias == null ? null : this;
  }  
  
  protected String getMatchingAlias(String argument) {
    for (String alias : getAliases()) {
      if (argument.startsWith(alias) && (argument.length() == alias.length() || argument.charAt(alias.length()) =='=' ) ) {
        return alias;
      }
    }
    return null;
  }
  
  public boolean acceptsPropterty(String propertyName) {
    if (propertyName.equals("default")) {
      return true;
    } else {
      return false;
    }
  }

  public void setProperty(String propertyName, String propertyValue) throws InvalidOptionPropertyValueException {
    if (propertyName.equals("default")) {
      try {
        this.setFromString(propertyValue);
      } catch (InvalidOptionValueException iove) {
        throw new InvalidOptionPropertyValueException("Invalid default value: " + iove.getMessage());
      }
    }
    //Else ignore
  }

  @Override
  public boolean equals(Object obj) {
    if (obj instanceof BasicOption) {
      this.getIdentifier().equals(((BasicOption)obj).getIdentifier());
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

}
