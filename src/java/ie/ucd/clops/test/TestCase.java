
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.clops.test;

import java.util.List;

public class TestCase extends BaseAST {



  private final Boolean condition;
  private final String testInput;

private final SourceLocation location;

  // === Constructors and Factories ===
  protected TestCase(Boolean condition, String testInput) {
    this(condition,testInput, null);    
  }

  protected TestCase(Boolean condition, String testInput, SourceLocation location) {
    this.location = location;
    this.condition = condition; assert condition != null;
    this.testInput = testInput; assert testInput != null;
    
  }
  
  public static TestCase mk(Boolean condition, String testInput) {
    return new TestCase(condition, testInput);
  }

  public static TestCase mk(Boolean condition, String testInput, SourceLocation location) {
    return new TestCase(condition, testInput, location);
  }

  // === Accessors ===

  public Boolean getCondition() { return condition; }
  public String getTestInput() { return testInput; }

  // === Others ===
  @Override
  public TestCase clone() {
    
      
        Boolean newCondition = condition;
      
    
      
        String newTestInput = testInput;
      
    
    return TestCase.mk(newCondition, newTestInput, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("TestCase ast node: ");
    
    sb.append("condition = ");
    sb.append(condition);
    sb.append(", ");
    
    sb.append("testInput = ");
    sb.append(testInput);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

