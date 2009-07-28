
/**
  This class is generated automatically from normal_classes.tpl. 
  Do not edit.
 */
package ie.ucd.clops.test;

import ie.ucd.clops.dsl.parser.SourceLocation;

import java.util.List;

public class TestSet extends BaseAST {



  private final String inputFileDirPath;
  private final String filePath;
  private final String name;
  private final List<TestCase> cases;

private final SourceLocation location;

  // === Constructors and Factories ===
  protected TestSet(String inputFileDirPath, String filePath, String name, List<TestCase> cases) {
    this(inputFileDirPath,filePath,name,cases, null);    
  }

  protected TestSet(String inputFileDirPath, String filePath, String name, List<TestCase> cases, SourceLocation location) {
    this.location = location;
    this.inputFileDirPath = inputFileDirPath; assert inputFileDirPath != null;
    this.filePath = filePath; assert filePath != null;
    this.name = name; assert name != null;
    this.cases = cases; 
    
  }
  
  public static TestSet mk(String inputFileDirPath, String filePath, String name, List<TestCase> cases) {
    return new TestSet(inputFileDirPath, filePath, name, cases);
  }

  public static TestSet mk(String inputFileDirPath, String filePath, String name, List<TestCase> cases, SourceLocation location) {
    return new TestSet(inputFileDirPath, filePath, name, cases, location);
  }

  // === Accessors ===

  public String getInputFileDirPath() { return inputFileDirPath; }
  public String getFilePath() { return filePath; }
  public String getName() { return name; }
  public List<TestCase> getCases() { return cases; }

  // === Others ===
  @Override
  public TestSet clone() {
    
      
        String newInputFileDirPath = inputFileDirPath;
      
    
      
        String newFilePath = filePath;
      
    
      
        String newName = name;
      
    
      
        List<TestCase> newCases = cases;
      
    
    return TestSet.mk(newInputFileDirPath, newFilePath, newName, newCases, location);
  }
  
  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("TestSet ast node: ");
    
    sb.append("inputFileDirPath = ");
    sb.append(inputFileDirPath);
    sb.append(", ");
    
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

