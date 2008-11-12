package ie.ucd.clops.dsl.generatedinterface;

import ie.ucd.clops.runtime.options.Option;
import ie.ucd.clops.runtime.options.OptionGroup;
import ie.ucd.clops.runtime.options.OptionStore;
import ie.ucd.clops.runtime.options.BooleanOption;
import ie.ucd.clops.runtime.options.OptionAssignment;
import ie.ucd.clops.runtime.flyrules.FlyRuleStore;

public class CLODSLParser extends ie.ucd.clops.runtime.parser.AbstractSpecificCLParser {
  final ie.ucd.clops.dsl.generatedinterface.CLODSLOptionStore optionStore;
  ie.ucd.clops.runtime.flyrules.FlyRuleStore flyRuleStore;
  public ie.ucd.clops.dsl.generatedinterface.CLODSLOptionStore getOptionStore() {
    return optionStore;
    
  }
  public ie.ucd.clops.runtime.flyrules.FlyRuleStore getFlyRuleStore() {
    return flyRuleStore;
    
  }
  public CLODSLParser() throws ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException {
    optionStore = createOptionStore();
    flyRuleStore = createFlyRuleStore();
    
  }
  private ie.ucd.clops.dsl.generatedinterface.CLODSLOptionStore createOptionStore() throws ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException {
    return new CLODSLOptionStore();
    
  }
  private FlyRuleStore createFlyRuleStore() {
    FlyRuleStore flyStore = new FlyRuleStore();
    return flyStore;
    
  }
  public String getFormatString() {
    return "( input output optional_args*) | ( output input optional_args*)";
    
  }
  
}
