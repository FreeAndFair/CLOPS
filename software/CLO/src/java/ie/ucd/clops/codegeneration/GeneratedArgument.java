package ie.ucd.clops.codegeneration;

public class GeneratedArgument {

  private final String argumentType;
  private final String argumentName;
  
  public GeneratedArgument(String argumentName, String argumentType) {
    this.argumentName = argumentName;
    this.argumentType = argumentType;
  }

  public String getArgumentType() {
    return argumentType;
  }

  public String getArgumentName() {
    return argumentName;
  }  
  
}
