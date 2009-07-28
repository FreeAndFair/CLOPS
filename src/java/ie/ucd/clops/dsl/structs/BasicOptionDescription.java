package ie.ucd.clops.dsl.structs;

import ie.ucd.clops.dsl.OptionType;
import ie.ucd.clops.dsl.parser.SourceLocation;
import ie.ucd.clops.util.Pair;

import java.util.LinkedList;
import java.util.List;

/**
 * @author Fintan
 *
 */
public class BasicOptionDescription implements OptionDescription {

  private final List<String> prefixRegexps;
  private String identifier;
  private final List<Pair<String,String>> properties;
  private OptionType type;
  private String description;
  private SourceLocation sourceLocation;

  public BasicOptionDescription() {
    this.prefixRegexps = new LinkedList<String>();
    this.properties = new LinkedList<Pair<String,String>>();
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
    prefixRegexps.add(alias);
  }
  
  /* (non-Javadoc)
   * @see ie.ucd.clo.dsl.structs.OptionDescription#getAliases()
   */
  public List<String> getPrefixRegexps() {
    return prefixRegexps;
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.dsl.structs.OptionDescription#setProperty(java.lang.String, java.lang.String)
   */
  public void setProperty(Pair<String,String> property) {
    properties.add(property);
  }

  public String getPropertyValue(String key) {
    String retv = null;
    for (Pair<String, String> p : properties) {
      if (p.getFirst().equals(key)) retv = p.getSecond();
    }
    return retv;
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.dsl.structs.OptionDescription#getProperties()
   */
  public List<Pair<String, String>> getProperties() {
    return properties;
  }
  
  
  /**
   * Set this option's String identifier.
   * @param id this options's identifier.
   */
  public void setId(final String id) {
    this.identifier = id.replaceAll("-", "_");
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
    for (String alias : prefixRegexps) {
      sb.append(alias);
      sb.append(", ");
    }
    if (prefixRegexps.size() > 0) {
      sb.delete(sb.length()-2, sb.length());
    }
    return sb.toString();
  }

  public String getDescription() {
    return description;
  }

  /**
   * Set the Option's textual description. 
   * @param description
   */
  public void setDescription(final String description) {
    this.description = description.replace("\n"," ").replace("\r"," ");
  }

  //Warning, currently a VERY naive implementation
  public List<String> getAliases() {
    return getPrefixRegexps();
  }
  
  public SourceLocation getSourceLocation() {
    return sourceLocation;
  }

  public void setSourceLocation(SourceLocation sourceLocation) {
    this.sourceLocation = sourceLocation;
  }
  
}
