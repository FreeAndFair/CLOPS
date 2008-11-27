package ie.ucd.clops.dsl.structs;

import ie.ucd.clops.dsl.OptionType;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

/**
 * @author Fintan
 *
 */
public class BasicOptionDescription implements OptionDescription {

  private final List<String> aliases;
  private String identifier;
  private final Map<String,String> properties;
  private OptionType type;

  public BasicOptionDescription() {
    this.aliases = new LinkedList<String>();
    this.properties = new HashMap<String,String>();
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
  public void addPrefixRegexp(final String alias) {
    aliases.add(alias);
  }
  
  /* (non-Javadoc)
   * @see ie.ucd.clo.dsl.structs.OptionDescription#getAliases()
   */
  public List<String> getPrefixRegexps() {
    return aliases;
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.dsl.structs.OptionDescription#setProperty(java.lang.String, java.lang.String)
   */
  public void setProperty(String key, String value) {
    properties.put(key, value);
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.dsl.structs.OptionDescription#getProperties()
   */
  public Map<String,String> getProperties() {
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
