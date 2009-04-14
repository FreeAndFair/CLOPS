package ie.ucd.clops.dsl.structs;


import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Simple AST-like datastructure for storing the information gathered
 * from parsing a DSL file.
 * 
 * Once all the informations are gathered the {@link #pack()} method
 * must be called to seal the object.
 * 
 * @author Fintan
 *
 */
public class DSLInformation extends RuleStore {
  /** true if the object is sealed (immutable). */ 
  private boolean isPacked;
  
  private String parserName;
  private String packageName;
  private String formatString;

  
  
  /** the structure containing correspondence between classes long and short names. */
  private NameDict dict = new NameDict();

  private String description = "";

  private String formatDesc = "";
  
  public DSLInformation() {
    parserName = "";
    packageName = "";
    isPacked = false;
  }

  public String getFormatString() {
    return formatString;
  }
  
  public void setFormatString(String formatString) {
    assert (!isPacked);
    this.formatString = formatString;
  }
  

  public String getParserName() {
    return parserName;
  }

  public void setParserName(String parserName) {
    assert (!isPacked);
    this.parserName = parserName;
  }

  public String getPackageName() {
    return packageName;
  }

  public void setPackageName(String packageName) {
    assert (!isPacked);
    this.packageName = packageName;
  }

  public Set<String> getTypeImports() {
    return dict.typeClzz;
  }
  public Set<String> getValueTypeImports() {
    return dict.valueClzz;
  }
  

  private static class NameDict {
    private final Map<String, String> clzzShrt = new HashMap<String, String>();
    private final Set<String> shrtz = new HashSet<String>();
    private final Set<String> valueClzz = new HashSet<String>();
    private final Set<String> typeClzz = new HashSet<String>();
    
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
  }
  
  public String getTypeClass(OptionDescription od) {
    return dict.clzzShrt.get(od.getType().getOptionTypeClass());
  }
  public String getValueTypeClass(OptionDescription od) {
    return dict.clzzShrt.get(od.getType().getOptionValueTypeClass());
  }
  
  
  @Override
  public void pack() {
    super.pack();
    /* Make sure no newlines in the format string. 
    This should probably be done whilst processing the DSL */
    setFormatString(formatString.replaceAll("\\n", " "));
    dict.computeImports(getOptionDescriptions());
    isPacked = true;
  }

  /**
   * Adds a description to the parser.
   * @param st the description string
   */
  public void setParserDescription(final String st) {
    assert (!isPacked);
    description = st;
  }

  public String getDescription() {
    return description;
  }
  
  /**
   * Adds a description to the parser.
   * @param st the description string
   */
  public void setFormatDescription(final String st) {
    assert (!isPacked);
    formatDesc = st;
  }
  public String getFormatDescription() {
    return formatDesc;
  }
  
}
