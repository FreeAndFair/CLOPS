package ie.ucd.clops.dsl.structs;

import java.util.ArrayList;
import java.util.Collection;

/**
 * AST-like information about an option group as specified in the CLOPS DSL.
 * @author Fintan
 *
 */
public class OptionGroupDescription {

  private final String identifier;
  private final Collection<String> children;

  public OptionGroupDescription(String identifier) {
    this.identifier = identifier;
    this.children = new ArrayList<String>();
  }

  public void addChild(String child) {
    children.add(child);
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
}
