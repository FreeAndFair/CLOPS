package ie.ucd.clops.dsl.structs;

import ie.ucd.clops.dsl.DefaultOptionTypeFactory;
import ie.ucd.clops.dsl.OptionType;
import ie.ucd.clops.dsl.structs.ast.OptionGroupChild;

import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * AST-like information about an option group as specified in the CLOPS DSL.
 * @author Fintan
 *
 */
public class OptionGroupDescription implements OptionDescription {

  private final String identifier;
  
  private Set<OptionGroupChild> children;
  
  private boolean isExpanded;

  public OptionGroupDescription(String identifier) {
    this.identifier = identifier;
    this.children = new HashSet<OptionGroupChild>();
    
    isExpanded = false;
  }

  public void addChild(OptionGroupChild child) {
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
  public Set<OptionGroupChild> getChildren() {
    return children;
  }

  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Group ");
    sb.append(identifier);
    sb.append(", children: ");
    for (OptionGroupChild child : children) {
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
    for (OptionGroupChild child : children) {
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
  
  public void expand(Map<String,OptionDescription> optionNameMap, Map<String,OptionGroupDescription> optionGroupNameMap) {
    if (isExpanded) {
      return;
    }
    //System.out.println("Before: " + children);
    Set<OptionGroupChild> newChildren = new HashSet<OptionGroupChild>();
    Set<OptionGroupChild> newChildrenRemoves = new HashSet<OptionGroupChild>();
    for (OptionGroupChild child : children) {
      OptionDescription op = optionNameMap.get(child.getName());
      if (op != null) {
        if (child.getAdd()) {
          newChildren.add(child);
        } else {
          newChildrenRemoves.add(child);
        }
      } else {
        OptionGroupDescription opGroup = optionGroupNameMap.get(child.getName());
        if (opGroup != null) {
          opGroup.expand(optionNameMap, optionGroupNameMap);
          if (child.getAdd()) {
            newChildren.addAll(opGroup.getChildren());
          } else {
            newChildrenRemoves.addAll(opGroup.getChildren());
          }
        }
      }
    }
    newChildren.removeAll(newChildrenRemoves);
    this.children = newChildren;
    this.isExpanded = true;
//    System.out.println("Updated " + identifier + " to " + children);
  }
}
