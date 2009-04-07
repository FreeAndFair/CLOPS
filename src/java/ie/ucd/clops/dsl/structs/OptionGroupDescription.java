package ie.ucd.clops.dsl.structs;

import ie.ucd.clops.dsl.DefaultOptionTypeFactory;
import ie.ucd.clops.dsl.OptionType;

import java.util.ArrayList;
import java.util.Collection;
import java.util.LinkedList;
import java.util.List;

/**
 * AST-like information about an option group as specified in the CLOPS DSL.
 * @author Fintan
 *
 */
public class OptionGroupDescription implements OptionDescription {

  private final String identifier;
  private final Collection<String> children;

  public OptionGroupDescription(String identifier) {
    this.identifier = identifier;
    this.children = new ArrayList<String>();
  }

  public void addChild(String child) {
    children.add(child.replaceAll("-", "_"));
  }

  /**
   * @return the identifier
   */
  public String getIdentifier() {
    return identifier;
  }

  /**
   * @return the identifiers of the sub-groups/options in this option group
   */
  public Collection<String> getChildren() {
    return children;
  }

  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Group ");
    sb.append(identifier);
    sb.append(", children: ");
    for (String child : children) {
      sb.append(child);
      sb.append(", ");
    }
    if (children.size() > 0) {
      sb.delete(sb.length() - 2, sb.length());
    }
    return sb.toString();
  }

  @Override
  public void addPrefixRegexp(String regexp) { }

  List<String> empty = new LinkedList<String>();
  @Override
  public List<String> getAliases() {
    return empty;
  }

  @Override
  public String getDescription() {
    final StringBuilder sb = new StringBuilder();
    for (String child : children) {
      sb.append(child);
      sb.append(", ");
    }
    if (children.size() > 0) {
      sb.delete(sb.length() - 2, sb.length());
    }
    return "{" + sb.toString() + "}";
  }

  @Override
  public List<String> getPrefixRegexps() {
    return empty;
  }

  List<Pair<String, String>> emptyPair = new LinkedList<Pair<String, String>>();
  @Override
  public List<Pair<String, String>> getProperties() {
    return emptyPair;
  }

  @Override
  public String getPropertyValue(String key) {
    return null;
  }

  @Override
  public OptionType getType() { // we are a sort of boolean
    return DefaultOptionTypeFactory.BOOLEAN;
  }

  @Override
  public void setDescription(String description) {
  }

  @Override
  public void setId(String id) {
  }

  @Override
  public void setProperty(String key, String value) {
  }

  @Override
  public void setType(OptionType type) {
  }
}
