package ie.ucd.clops.dsl.structs;


import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Simple AST-like datastructure for storing the information gathered
 * from parsing a DSL file.
 * 
 * @author Fintan
 *
 */
public class DSLInformation {

  public boolean TRANSITIVE_FLYRULES;

  private final List<OptionDescription> optionDescriptions;
  private final Map<String,OptionDescription> optionIdDescriptionMap;
  private final List<OptionGroupDescription> optionGroupDescriptions;
  private final List<FlyRuleDescription> flyRuleDescriptions;
  private final List<OverrideRuleDescription> overrideRuleDescriptions;
  private final List<ValidityRuleDescription> validityRuleDescriptions;
  private String parserName;
  private String packageName;
  private String formatString;
  
  public DSLInformation() {
    optionDescriptions = new LinkedList<OptionDescription>();
    optionIdDescriptionMap = new HashMap<String, OptionDescription>();
    optionGroupDescriptions = new LinkedList<OptionGroupDescription>();
    flyRuleDescriptions = new LinkedList<FlyRuleDescription>();
    overrideRuleDescriptions = new LinkedList<OverrideRuleDescription>();
    validityRuleDescriptions = new LinkedList<ValidityRuleDescription>();
    parserName = "";
    packageName = "";
  }

  public boolean getTransitive_Flyrules() { return TRANSITIVE_FLYRULES; }

  public String getFormatString() {
    return formatString;
  }
  
  public void setFormatString(String formatString) {
    this.formatString = formatString;
  }
  
  public void addOptionDescription(OptionDescription optionDescription) {
    optionDescriptions.add(optionDescription);
    optionIdDescriptionMap.put(optionDescription.getIdentifier(), optionDescription);
  }
  
  public List<OptionDescription> getOptionDescriptions() {
    return optionDescriptions;
  }
  
  public void addOptionGroupDescription(OptionGroupDescription optionGroupDescription) {
    optionGroupDescriptions.add(optionGroupDescription);
  }
  
  public List<OptionGroupDescription> getOptionGroupDescriptions() {
    return optionGroupDescriptions;
  }
  
  public void addFlyRuleDescription(FlyRuleDescription flyRuleDescription) {
    flyRuleDescriptions.add(flyRuleDescription);
  }
  
  public void addOverrideRuleDescription(OverrideRuleDescription overrideRuleDescription) {
    overrideRuleDescriptions.add(overrideRuleDescription);
  }
    
  public void addValidityRuleDescription(ValidityRuleDescription validityRuleDescription) {
    validityRuleDescriptions.add(validityRuleDescription);
  }
  
  public List<FlyRuleDescription> getFlyRuleDescriptions() {
    return flyRuleDescriptions;
  }

  public String getParserName() {
    return parserName;
  }

  public void setParserName(String parserName) {
    this.parserName = parserName;
  }

  public String getPackageName() {
    return packageName;
  }

  public void setPackageName(String packageName) {
    this.packageName = packageName;
  }
  
  public OptionDescription getOptionDescriptionForIdentifier(String identifier) {
    return optionIdDescriptionMap.get(identifier);
  }
  
  public String getOptionValuTypeParameterisationForIdentifier(String identifier) {
    OptionDescription od = getOptionDescriptionForIdentifier(identifier);
    return od == null ? null : od.getType().getOptionValueTypeParameterisation();
  }

  public List<OverrideRuleDescription> getOverrideRuleDescriptions() {
    return overrideRuleDescriptions;
  }

  public List<ValidityRuleDescription> getValidityRuleDescriptions() {
    return validityRuleDescriptions;
  }
  
  
  public Set<String> getImports() {
    for (OptionDescription od: getOptionDescriptions()) {
      // we check everything' s there
      String clzz = od.getType().getOptionTypeClass();
      getShortClassName(clzz);
      clzz = od.getType().getOptionValueTypeClass();
      getShortClassName(clzz);
    }
    return lngClzz;
  }
  
  final Map<String, String> clzzShrt = new HashMap<String, String>();
  final Set<String> shrtz = new HashSet<String>();
  final Set<String> lngClzz = new HashSet<String>();
  
  private String getShortClassName(String clzz) {
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
        if (generics > 0) {
          clzz = clzz.substring(0, generics);
        }
        lngClzz.add(clzz);
      }
      shrtz.add(shrt);
      
    }
    return shrt;
  }

  public String getTypeClass(OptionDescription od) {
    return getShortClassName(od.getType().getOptionTypeClass());
  }
  public String getValueTypeClass(OptionDescription od) {
    return getShortClassName(od.getType().getOptionValueTypeClass());
  }
  
  private boolean isJavaLang(String clzz) {
    return clzz.startsWith("java.lang") || clzz.equals("String");
  }

  private boolean isPrimitive(String clzz) {
    return clzz.equals("boolean");
  }

  public void processPlaceholders() {
    for (RuleDescription rule : flyRuleDescriptions) rule.processPlaceHolders(this);
    for (RuleDescription rule : overrideRuleDescriptions) rule.processPlaceHolders(this);
    for (ValidityRuleDescription rule : validityRuleDescriptions) rule.processPlaceHolders(this);
  }
  
}
