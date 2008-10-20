package ie.ucd.clops.codegeneration;

import java.util.LinkedList;
import java.util.List;

public class GeneratedClass extends GeneratedCodeUnit {

  private final List<GeneratedMethod> methods;
  private final List<GeneratedField> fields;
  private final List<String> imports;
  private String superClass;
  
  public GeneratedClass(String name) {
    super(name);
    this.methods = new LinkedList<GeneratedMethod>();
    this.fields = new LinkedList<GeneratedField>();
    this.imports = new LinkedList<String>();
    this.superClass = null;
  }
  
  public GeneratedClass(String name, Visibility visibility) {
    super(name, visibility); 
    this.methods = new LinkedList<GeneratedMethod>();
    this.fields = new LinkedList<GeneratedField>();
    this.imports = new LinkedList<String>();
  }

  public List<GeneratedMethod> getMethods() {
    return methods;
  }

  public List<GeneratedField> getFields() {
    return fields;
  }  

  public List<String> getImports() {
    return imports;
  }

  public void addMethod(GeneratedMethod genMethod) {
    methods.add(genMethod);
  }
  
  public void addField(GeneratedField genField) {
    fields.add(genField);
  }
  
  public void addImport(String im) {
    imports.add(im);
  }
  
  public void setSuperClass(String superClass) {
    this.superClass = superClass;
  }

  public String getSuperClass() {
    return superClass;
  }
  
}
