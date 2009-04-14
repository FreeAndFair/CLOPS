package ie.ucd.clops.dsl.structs;

import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * A dictionnary to compute the import lists.
 * @author J. Charles
 */
public class NameDict {
  private final Map<String, String> clzzShrt = 
    new HashMap<String, String>();
  private final Set<String> shrtz = new HashSet<String>();
  private final Set<String> valueClzz = new HashSet<String>();
  private final Set<String> typeClzz = new HashSet<String>();
  
  public NameDict(List<OptionDescription> desc) {
    computeImports(desc);
  }
  
  private void computeImports(List<OptionDescription> desc) {
    for (OptionDescription od: desc) {
      // we check everything' s there
      String clzz = od.getType().getOptionTypeClass();
      getShortClassName(clzz, typeClzz);
      clzz = od.getType().getOptionValueTypeClass();
      getShortClassName(clzz, valueClzz);
    }
  }

  private String getShortClassName(final String clzz, Set<String> lngClzz) {
    String shrt = clzzShrt.get(clzz);
    
    if (shrt != null) {
      return shrt;
    }
    final int generics = clzz.lastIndexOf('<');
    String genfree = clzz;
    if (generics > 0) {
      genfree = clzz.substring(0, generics);
    }
    shrt = clzz.substring(genfree.lastIndexOf('.') + 1);
    if (shrtz.contains(shrt)) {
      shrt = clzz;
      clzzShrt.put(clzz, clzz);
    }
    else {

      clzzShrt.put(clzz, shrt);
      if (!isPrimitive(clzz) && !isJavaLang(clzz)) {
        String withoutgen = clzz;
        if (generics > 0) {
          withoutgen = withoutgen.substring(0, generics);
        }
        lngClzz.add(withoutgen);
      }
      shrtz.add(shrt);
      
    }
    return shrt;
  }


  
  private static boolean isJavaLang(final String clzz) {
    return clzz.startsWith("java.lang") || clzz.equals("String");
  }

  private static boolean isPrimitive(final String clzz) {
    return clzz.equals("boolean") || clzz.equals("int") || 
           clzz.equals("float") || clzz.equals("double") || 
           clzz.equals("long") || clzz.equals("short") || 
           clzz.equals("byte") || clzz.equals("char");
  }
  
  public String getTypeClass(OptionDescription od) {
    return clzzShrt.get(od.getType().getOptionTypeClass());
  }
  
  public String getValueTypeClass(OptionDescription od) {
    return clzzShrt.get(od.getType().getOptionValueTypeClass());
  }
  public Set<String> getTypeImports() {
    return typeClzz;
  }
  public Set<String> getValueTypeImports() {
    return valueClzz;
  }
  
}