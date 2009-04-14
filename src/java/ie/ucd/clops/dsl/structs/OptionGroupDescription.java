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
  /** used with the method {@link #getAliases()} 
      and {@link #getPrefixRegexps()} . */
  private static final List<String> empty = new LinkedList<String>();
  
  /** the identifier associated with this group. */
  private final String identifier;
 
  /** the properties associated with this Group. */
  private final List<Pair<String, String>> prop = new LinkedList<Pair<String, String>>();

  //TODO: add description
  private final Set<OptionGroupChild> ogChildren;
  //TODO: add description
  private final Set<String> children;
  
  /** true if the children have already been computed. */
  private boolean isExpanded;
  
  

  public OptionGroupDescription(String identifier) {
    this.identifier = identifier;
    
    ogChildren = new HashSet<OptionGroupChild>();
    children = new HashSet<String>();
    isExpanded = false;
  }
  
  public void addChild(final OptionGroupChild child) {
    ogChildren.add(child);
  }

  /** {@inheritDoc} */
  @Override
  public String getIdentifier() {
    return identifier;
  }

  /**
   * @return the identifiers of the sub-groups/options in this option group
   */
  public Set<String> getChildren() {
    return children;
  }

  /** {@inheritDoc} */
  @Override
  public String toString() {
    final StringBuilder sb = new StringBuilder();
    sb.append("Group ");
    sb.append(identifier);
    sb.append(", children: ");
    for (OptionGroupChild child : ogChildren) {
      sb.append(child);
      sb.append(", ");
    }
    if (ogChildren.size() > 0) {
      sb.delete(sb.length() - 2, sb.length());
    }
    return sb.toString();
  }

  /** {@inheritDoc} */
  @Override
  public void addPrefixRegexp(final String regexp) { }

  

  
  /** {@inheritDoc} */
  @Override
  public String getDescription() {
    final StringBuilder sb = new StringBuilder();
    for (OptionGroupChild child : ogChildren) {
      sb.append(child);
      sb.append(", ");
    }
    if (ogChildren.size() > 0) {
      sb.delete(sb.length() - 2, sb.length());
    }
    return "{" + sb.toString() + "}";
  }
  
  


  /** {@inheritDoc} */
  @Override
  public List<Pair<String, String>> getProperties() {
    return prop;
  }

  /** {@inheritDoc} */
  @Override
  public String getPropertyValue(final String key) {
    String retv = null;
    for (Pair<String, String> p : prop) {
      if (p.getFirst().equals(key)) {
        retv = p.getSecond();
      }
    }
    return retv;
  }

  /** {@inheritDoc} */
  @Override
  public OptionType getType() { // we are a sort of boolean
    return DefaultOptionTypeFactory.BOOLEAN;
  }


  /** {@inheritDoc} */
  @Override
  public void setProperty(final String key, final String value) {
    prop.add(new Pair<String, String>(key, value));
  }
  
  // TODO: need review
  public void expand(final Map<String, OptionDescription> optionNameMap, 
                     final Map<String, OptionGroupDescription> optionGroupNameMap) {
    if (isExpanded) {
      return;
    }
    this.isExpanded = true;
    //System.out.println("Before: " + children);
    children.clear(); //Just to be sure
    final Set<String> newChildrenRemoves = new HashSet<String>();
    for (OptionGroupChild child : ogChildren) {
      final OptionDescription op = optionNameMap.get(child.getName());
      if (op != null) {
        if (child.getAdd()) {
          children.add(child.getName());
        } 
        else {
          newChildrenRemoves.add(child.getName());
        }
      } 
      else {
        final OptionGroupDescription opGroup = optionGroupNameMap.get(child.getName());
        if (opGroup != null) {
          opGroup.expand(optionNameMap, optionGroupNameMap);
          if (child.getAdd()) {
            children.addAll(opGroup.getChildren());
          } 
          else {
            newChildrenRemoves.addAll(opGroup.getChildren());
          }
        } 
        else {
          if (child.getName().equals("AllOptions")) {
            if (child.getAdd()) {
              children.addAll(optionNameMap.keySet());
            } 
            else {
              newChildrenRemoves.addAll(optionNameMap.keySet());
            }
          }
        }
      } 
    }
    children.removeAll(newChildrenRemoves);

//    System.out.println("Updated " + identifier + " to " + children);
  }
  
  // TODO should be removed
  @Override
  public List<String> getPrefixRegexps() {
    return empty;
  }
  
  // TODO should be removed
  @Override
  public List<String> getAliases() {
    return empty;
  }
}
