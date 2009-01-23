package ie.ucd.clops.dsl.generatedinterface;

import ie.ucd.clops.runtime.rules.*;
import ie.ucd.clops.runtime.options.*;

public class CLODSLRuleStore extends ie.ucd.clops.runtime.rules.RuleStore {

  public CLODSLRuleStore() {
    

  
    Expression<Boolean> rule1Condition = new Rule1Condition();
    ValidityRule rule1 = new ValidityRule(rule1Condition);
    rule1.addAction(new Action<java.util.List<String>>("CLOPSERROROPTION", new Rule1Expression()));
    addValidityRule(rule1);
    Expression<Boolean> rule2Condition = new Rule2Condition();
    ValidityRule rule2 = new ValidityRule(rule2Condition);
    rule2.addAction(new Action<java.util.List<String>>("CLOPSERROROPTION", new Rule2Expression()));
    addValidityRule(rule2);
  }


  
    public static class Rule1Condition implements Expression<Boolean> {
      public Boolean evaluate(OptionStore optionStore) {
        return !((ie.ucd.clops.runtime.options.FileOption)optionStore.getOptionByIdentifier("input")).hasValue();
      }
    }
    
    public static class Rule1Expression implements Expression<java.util.List<String>> {
      public java.util.List<String> evaluate(OptionStore optionStore) {
        return java.util.Arrays.asList("input not set");
      }
    }
    public static class Rule2Condition implements Expression<Boolean> {
      public Boolean evaluate(OptionStore optionStore) {
        return !((ie.ucd.clops.runtime.options.FileOption)optionStore.getOptionByIdentifier("output")).hasValue();
      }
    }
    
    public static class Rule2Expression implements Expression<java.util.List<String>> {
      public java.util.List<String> evaluate(OptionStore optionStore) {
        return java.util.Arrays.asList("output not set");
      }
    }

}