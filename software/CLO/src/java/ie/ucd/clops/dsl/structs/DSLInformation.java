package ie.ucd.clops.dsl.structs;


import java.util.Collection;
import java.util.LinkedList;

/**
 * Simple AST-like datastructure for storing the information gathered
 * from parsing a DSL file.
 * 
 * @author Fintan
 *
 */
public class DSLInformation {

  private final Collection<OptionDescription> optionDescriptions;
  private final Collection<OptionGroupDescription> optionGroupDescriptions;
  private final Collection<FlyRuleDescription> flyRuleDescriptions;
  private String parserName;
  private String packageName;
  private String formatString;
  
  public DSLInformation() {
    optionDescriptions = new LinkedList<OptionDescription>();
    optionGroupDescriptions = new LinkedList<OptionGroupDescription>();
    flyRuleDescriptions = new LinkedList<FlyRuleDescription>();
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
  }
  
  public Collection<OptionDescription> getOptionDescriptions() {
    return optionDescriptions;
  }
  
  public void addOptionGroupDescription(OptionGroupDescription optionGroupDescription) {
    optionGroupDescriptions.add(optionGroupDescription);
  }
  
  public Collection<OptionGroupDescription> getOptionGroupDescriptions() {
    return optionGroupDescriptions;
  }
  
  public void addFlyRuleDescription(FlyRuleDescription flyRuleDescription) {
    flyRuleDescriptions.add(flyRuleDescription);
  }
  
  public Collection<FlyRuleDescription> getFlyRuleDescriptions() {
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
  
}
