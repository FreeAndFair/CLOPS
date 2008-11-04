package ie.ucd.clops.dsl.structs;

import ie.ucd.clops.runtime.options.OptionType;

import java.util.HashSet;
import java.util.Properties;
import java.util.Set;

/**
 * @author Fintan
 *
 */
public class BasicOptionDescription implements OptionDescription {

  private final Set<String> aliases;
  private String identifier;
  private final Properties properties;
  private OptionType type;

  public BasicOptionDescription() {
    this.aliases = new HashSet<String>();
    this.properties = new Properties();
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.dsl.structs.OptionDescription#getId()
   */
  public String getIdentifier() {
    return identifier;
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.dsl.structs.OptionDescription#getType()
   */
  public OptionType getType() {
    return type;
  }
  
  /* (non-Javadoc)
   * @see ie.ucd.clo.dsl.structs.OptionDescription#addAlias(java.lang.String)
   */
  public void addAlias(final String alias) {
    aliases.add(alias);
  }
  
  /* (non-Javadoc)
   * @see ie.ucd.clo.dsl.structs.OptionDescription#getAliases()
   */
  public Set<String> getAliases() {
    return aliases;
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.dsl.structs.OptionDescription#setProperty(java.lang.String, java.lang.String)
   */
  public void setProperty(String key, String value) {
    properties.setProperty(key, value);
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.dsl.structs.OptionDescription#getProperties()
   */
  public Properties getProperties() {
    return properties;
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.dsl.structs.OptionDescription#setId(java.lang.String)
   */
  public void setId(String id) {
    this.identifier = id;
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.dsl.structs.OptionDescription#setType(ie.ucd.clo.dsl.structs.OptionType)
   */
  public void setType(OptionType type) {
    this.type = type;
  }

  /* (non-Javadoc)
   * @see java.lang.Object#toString()
   */
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Option ");
    sb.append(identifier);
    sb.append(", aliases: ");
    for (String alias : aliases) {
      sb.append(alias);
      sb.append(", ");
    }
    if (aliases.size() > 0) {
      sb.delete(sb.length()-2, sb.length());
    }
    return sb.toString();
  }  
  
  
}
