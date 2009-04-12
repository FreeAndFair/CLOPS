
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.clops.dsl.structs.ast;

import java.util.List;

public class OptionGroupChild extends BaseAST {



  private final String name;
  private final Boolean add;

private final SourceLocation location;

  // === Constructors and Factories ===
  protected OptionGroupChild(String name, Boolean add) {
    this(name,add, null);    
  }

  protected OptionGroupChild(String name, Boolean add, SourceLocation location) {
    this.location = location;
    this.name = name; assert name != null;
    this.add = add; assert add != null;
    
  }
  
  public static OptionGroupChild mk(String name, Boolean add) {
    return new OptionGroupChild(name, add);
  }

  public static OptionGroupChild mk(String name, Boolean add, SourceLocation location) {
    return new OptionGroupChild(name, add, location);
  }

  // === Accessors ===

  public String getName() { return name; }
  public Boolean getAdd() { return add; }

  // === Others ===
  @Override
  public OptionGroupChild clone() {
    
      
        String newName = name;
      
    
      
        Boolean newAdd = add;
      
    
    return OptionGroupChild.mk(newName, newAdd, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("OptionGroupChild ast node: ");
    
    sb.append("name = ");
    sb.append(name);
    sb.append(", ");
    
    sb.append("add = ");
    sb.append(add);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

