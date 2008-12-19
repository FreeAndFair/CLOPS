
package ie.ucd.clops.dsl.generatedinterface;

public class CLODSLParser extends ie.ucd.clops.runtime.parser.AbstractSpecificCLParser {
  final ie.ucd.clops.dsl.generatedinterface.CLODSLOptionStore optionStore;
  ie.ucd.clops.runtime.rules.RuleStore ruleStore;
  
  public ie.ucd.clops.dsl.generatedinterface.CLODSLOptionStore getOptionStore() {
    return optionStore;
    
  }
  
  public ie.ucd.clops.runtime.rules.RuleStore getRuleStore() {
    return ruleStore;
    
  }
  
  public CLODSLParser() throws ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException {
    optionStore = createOptionStore();
    ruleStore = createRuleStore();
    
  }
  
  private ie.ucd.clops.dsl.generatedinterface.CLODSLOptionStore createOptionStore() throws ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException {
    return new CLODSLOptionStore();
    
  }
  
  private ie.ucd.clops.runtime.rules.RuleStore createRuleStore() {
    return new CLODSLRuleStore();
    
  }
  
  public String getFormatString() {
    return "all_args*";
    
  }
  
}
