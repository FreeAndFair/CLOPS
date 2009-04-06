
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.clops.test;

import java.util.List;

public class TestSet extends BaseAST {



  private final String filePath;
  private final String name;
  private final List<TestCase> cases;

private final SourceLocation location;

  // === Constructors and Factories ===
  protected TestSet(String filePath, String name, List<TestCase> cases) {
    this(filePath,name,cases, null);    
  }

  protected TestSet(String filePath, String name, List<TestCase> cases, SourceLocation location) {
    this.location = location;
    this.filePath = filePath; assert filePath != null;
    this.name = name; assert name != null;
    this.cases = cases; 
    
  }
  
  public static TestSet mk(String filePath, String name, List<TestCase> cases) {
    return new TestSet(filePath, name, cases);
  }

  public static TestSet mk(String filePath, String name, List<TestCase> cases, SourceLocation location) {
    return new TestSet(filePath, name, cases, location);
  }

  // === Accessors ===

  public String getFilePath() { return filePath; }
  public String getName() { return name; }
  public List<TestCase> getCases() { return cases; }

  // === Others ===
  @Override
  public TestSet clone() {
    
      
        String newFilePath = filePath;
      
    
      
        String newName = name;
      
    
      
        List<TestCase> newCases = cases;
      
    
    return TestSet.mk(newFilePath, newName, newCases, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("TestSet ast node: ");
    
    sb.append("filePath = ");
    sb.append(filePath);
    sb.append(", ");
    
    sb.append("name = ");
    sb.append(name);
    sb.append(", ");
    
    sb.append("cases = ");
    sb.append(cases);
    sb.append(", ");
    
    if (sb.length() >= 2) {
      sb.delete(sb.length()-2,sb.length());
    }
    return sb.toString();
  }
}

