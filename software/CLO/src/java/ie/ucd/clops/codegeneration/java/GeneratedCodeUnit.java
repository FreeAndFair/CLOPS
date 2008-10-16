package ie.ucd.clops.codegeneration.java;

import java.util.LinkedList;
import java.util.List;

public class GeneratedCodeUnit {

  public enum Visibility { Public, Protected, PackagePrivate, Private }; 
  
  private Visibility visibility;
  private final String name;
  private final List<String> modifiers;

  public GeneratedCodeUnit(String name) {
    this(name, Visibility.PackagePrivate);
  }
  
  public GeneratedCodeUnit(String name, Visibility visibility) {
    this.visibility = visibility;
    this.name = name;
    this.modifiers = new LinkedList<String>();
  }
  
  public Visibility getVisibility() {
    return visibility;
  }

  public void setVisibility(Visibility visibility) {
    this.visibility = visibility;
  }

  public String getName() {
    return name;
  }

  public List<String> getModifiers() {
    return modifiers;
  }  
  
}
