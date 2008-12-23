package ie.ucd.clops.dsl.generatedinterface;

import ie.ucd.clops.runtime.parser.AbstractSpecificCLParser;
import ie.ucd.clops.runtime.rules.RuleStore;

public class CLODSLParser extends AbstractSpecificCLParser { 
  private final CLODSLOptionStore optionStore;
  private final ie.ucd.clops.runtime.rules.RuleStore ruleStore;

  public CLODSLParser() throws ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException {
    optionStore = new CLODSLOptionStore();
    ruleStore = new CLODSLRuleStore(); 
  }

  public CLODSLOptionStore getOptionStore() {
    return optionStore;  
  }
  
  public RuleStore getRuleStore() {
    return ruleStore;
  }
  
  public String getFormatString() {
    return "all_args*"; 
  }
}