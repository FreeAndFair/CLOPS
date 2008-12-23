package ie.ucd.clops.dsl.structs;


import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

/**
 * Simple AST-like datastructure for storing the information gathered
 * from parsing a DSL file.
 * 
 * @author Fintan
 *
 */
public class DSLInformation {

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
    optionIdDescriptionMap = new HashMap<String,OptionDescription>();
    optionGroupDescriptions = new LinkedList<OptionGroupDescription>();
    flyRuleDescriptions = new LinkedList<FlyRuleDescription>();
    overrideRuleDescriptions = new LinkedList<OverrideRuleDescription>();
    validityRuleDescriptions = new LinkedList<ValidityRuleDescription>();
    parserName = "";
    packageName = "";
  }
  
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
  
  public void processPlaceholders() {
    for (RuleDescription rule : flyRuleDescriptions) rule.processPlaceHolders(this);
    for (RuleDescription rule : overrideRuleDescriptions) rule.processPlaceHolders(this);
    for (RuleDescription rule : validityRuleDescriptions) rule.processPlaceHolders(this);
  }
  
}
