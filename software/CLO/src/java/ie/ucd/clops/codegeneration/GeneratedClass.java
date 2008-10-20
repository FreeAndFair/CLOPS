package ie.ucd.clops.codegeneration;

import java.util.LinkedList;
import java.util.List;

public class GeneratedClass extends GeneratedCodeUnit {

  private final List<GeneratedMethod> methods;
  private final List<GeneratedField> fields;
  
  public GeneratedClass(String name) {
    super(name);
    this.methods = new LinkedList<GeneratedMethod>();
    this.fields = new LinkedList<GeneratedField>();
  }
  
  public GeneratedClass(String name, Visibility visibility) {
    super(name, visibility); 
    this.methods = new LinkedList<GeneratedMethod>();
    this.fields = new LinkedList<GeneratedField>();
  }

  public List<GeneratedMethod> getMethods() {
    return methods;
  }

  public List<GeneratedField> getFields() {
    return fields;
  }  

  public void addMethod(GeneratedMethod genMethod) {
    methods.add(genMethod);
  }
  
  public void addField(GeneratedField genField) {
    fields.add(genField);
  }  
  
}
