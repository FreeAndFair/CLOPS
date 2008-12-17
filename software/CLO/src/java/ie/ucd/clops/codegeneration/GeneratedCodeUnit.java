package ie.ucd.clops.codegeneration;

import java.util.HashSet;
import java.util.Set;

public class GeneratedCodeUnit {

  public enum Visibility { Public, Protected, PackagePrivate, Private }; 
  
  private Visibility visibility;
  private final String name;
  private final Set<String> modifiers;

  public GeneratedCodeUnit(String name) {
    this(name, Visibility.PackagePrivate);
  }
  
  public GeneratedCodeUnit(String name, Visibility visibility) {
    this.visibility = visibility;
    this.name = name.replaceAll("-", "_");
    this.modifiers = new HashSet<String>();
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

  public Set<String> getModifiers() {
    return modifiers;
  }  
  
  public void addModifier(String modifier) {
    modifiers.add(modifier);
  }
}
