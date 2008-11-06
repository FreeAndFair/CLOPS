package ie.ucd.clops.codegeneration;

import java.util.LinkedList;
import java.util.List;

public class GeneratedClassOrInterface extends GeneratedCodeUnit {

  private final List<GeneratedMethod> methods;
  private final List<GeneratedField> fields;
  private final List<String> imports;
  private final String packageName;
  private final boolean isInterface;
  private final List<String> implementedInterfaces;
  private String superClass;
  
  public GeneratedClassOrInterface(String name, boolean isInterface, String packageName) {
    super(name);
    this.isInterface = isInterface;
    this.methods = new LinkedList<GeneratedMethod>();
    this.fields = new LinkedList<GeneratedField>();
    this.imports = new LinkedList<String>();
    this.implementedInterfaces = new LinkedList<String>();
    this.packageName = packageName;
    this.superClass = null;
  }
  
  public GeneratedClassOrInterface(String name, boolean isInterface, String packageName, Visibility visibility) {
    super(name, visibility);
    this.isInterface = isInterface;
    this.methods = new LinkedList<GeneratedMethod>();
    this.fields = new LinkedList<GeneratedField>();
    this.imports = new LinkedList<String>();
    this.implementedInterfaces = new LinkedList<String>();
    this.packageName = packageName;
    this.superClass = null;
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

  public List<String> getImplementedInterfaces() {
    return implementedInterfaces;
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
  
  public void addImplementedInterface(String interfaceName) {
    implementedInterfaces.add(interfaceName);
  }
  
  public void setSuperClass(String superClass) {
    this.superClass = superClass;
  }

  public String getSuperClass() {
    return superClass;
  }

  public String getPackageName() {
    return packageName;
  }

  public boolean isInterface() {
    return isInterface;
  }
  
  
  
}
