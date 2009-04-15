package ie.ucd.clops.dsl.generatedinterface;

import ie.ucd.clops.runtime.options.OptionStore;
import ie.ucd.clops.runtime.rules.Action;
import ie.ucd.clops.runtime.rules.Expression;
import ie.ucd.clops.runtime.rules.FlyRule;
import ie.ucd.clops.runtime.rules.OverrideRule;
import ie.ucd.clops.runtime.rules.RuleStore;
import ie.ucd.clops.runtime.rules.ValidityRule;


import java.util.Arrays;
import java.util.List;

/**
 * The rule store is used to handle the constraints and the validity
 * checks associated with the options.
 * @author The CLOPS team (kind@ucd.ie)
 */
public class CLODSLRuleStore extends RuleStore {
  
  public CLODSLRuleStore() {
    Expression<Boolean> rule1Condition = new Rule1Condition();
    ValidityRule rule1 = new ValidityRule(rule1Condition);
    rule1.addAction(new Action<List<String>>("CLOPSERROROPTION", new Rule1Expression()));
    addValidityRule(rule1);
  }

  public static class Rule1Condition implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(final OptionStore optionStore) {
      return !((ie.ucd.clops.runtime.options.FileOption)optionStore.getOptionByIdentifier("Output")).hasValue();
    }
  }
    
  public static class Rule1Expression implements Expression<List<String>> {
    /**
     * {@inheritDoc}
     */
    public List<String> evaluate(final OptionStore optionStore) {
      return Arrays.asList("The output should always be set to a valid value");
    }
  }
  

  protected final boolean shouldApplyFlyRulesTransitively() {
    return false;
  }
}
