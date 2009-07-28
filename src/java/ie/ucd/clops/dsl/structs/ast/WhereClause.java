
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.clops.dsl.structs.ast;

import ie.ucd.clops.dsl.parser.SourceLocation;
import java.util.List;

public class WhereClause extends BaseAST {



  private final String groupName;
  private final List<OptionGroupChild> children;

private final SourceLocation location;

  // === Constructors and Factories ===
  protected WhereClause(String groupName, List<OptionGroupChild> children) {
    this(groupName,children, null);    
  }

  protected WhereClause(String groupName, List<OptionGroupChild> children, SourceLocation location) {
    this.location = location;
    this.groupName = groupName; assert groupName != null;
    this.children = children; 
    
  }
  
  public static WhereClause mk(String groupName, List<OptionGroupChild> children) {
    return new WhereClause(groupName, children);
  }

  public static WhereClause mk(String groupName, List<OptionGroupChild> children, SourceLocation location) {
    return new WhereClause(groupName, children, location);
  }

  // === Accessors ===

  public String getGroupName() { return groupName; }
  public List<OptionGroupChild> getChildren() { return children; }

  // === Others ===
  @Override
  public WhereClause clone() {
    
      
        String newGroupName = groupName;
      
    
      
        List<OptionGroupChild> newChildren = children;
      
    
    return WhereClause.mk(newGroupName, newChildren, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("WhereClause ast node: ");
    
    sb.append("groupName = ");
    sb.append(groupName);
    sb.append(", ");
    
    sb.append("children = ");
    sb.append(children);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

