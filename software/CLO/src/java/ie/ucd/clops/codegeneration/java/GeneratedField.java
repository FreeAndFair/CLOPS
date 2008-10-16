package ie.ucd.clops.codegeneration.java;

public class GeneratedField extends GeneratedCodeUnit {

  private final String type;
  
  public GeneratedField(String name, String type, Visibility visibility) {
    super(name, visibility);
    this.type = type;
  }

  public GeneratedField(String name, String type) {
    super(name);
    this.type = type;
  }

  public String getType() {
    return type;
  }  
  
}
