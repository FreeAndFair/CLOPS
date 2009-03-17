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
    Expression<Boolean> rule2Condition = new Rule2Condition();
    ValidityRule rule2 = new ValidityRule(rule2Condition);
    rule2.addAction(new Action<List<String>>("CLOPSERROROPTION", new Rule2Expression()));
    addValidityRule(rule2);
    Expression<Boolean> rule3Condition = new Rule3Condition();
    ValidityRule rule3 = new ValidityRule(rule3Condition);
    rule3.addAction(new Action<List<String>>("CLOPSERROROPTION", new Rule3Expression()));
    addValidityRule(rule3);
    Expression<Boolean> rule4Condition = new Rule4Condition();
    ValidityRule rule4 = new ValidityRule(rule4Condition);
    rule4.addAction(new Action<List<String>>("CLOPSERROROPTION", new Rule4Expression()));
    addValidityRule(rule4);
    Expression<Boolean> rule5Condition = new Rule5Condition();
    ValidityRule rule5 = new ValidityRule(rule5Condition);
    rule5.addAction(new Action<List<String>>("CLOPSERROROPTION", new Rule5Expression()));
    addValidityRule(rule5);
  }

  public static class Rule1Condition implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(final OptionStore optionStore) {
      return !((ie.ucd.clops.runtime.options.FileOption)optionStore.getOptionByIdentifier("output")).hasValue();
    }
  }
    
  public static class Rule1Expression implements Expression<List<String>> {
    /**
     * {@inheritDoc}
     */
    public List<String> evaluate(final OptionStore optionStore) {
      return Arrays.asList("output not set");
    }
  }
  
  public static class Rule2Condition implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(final OptionStore optionStore) {
      return ie.ucd.clops.runtime.rules.Util.countSetOptions(new String[] { "gen_docs_builtin", "gen_docs_custom" }, optionStore) > 1;
    }
  }
    
  public static class Rule2Expression implements Expression<List<String>> {
    /**
     * {@inheritDoc}
     */
    public List<String> evaluate(final OptionStore optionStore) {
      return Arrays.asList("Only one type of documentation template may be used.");
    }
  }
  
  public static class Rule3Condition implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(final OptionStore optionStore) {
      return ((ie.ucd.clops.runtime.options.FileOption)optionStore.getOptionByIdentifier("gen_docs")).hasValue() ? !(((ie.ucd.clops.runtime.options.StringEnumOption)optionStore.getOptionByIdentifier("gen_docs_builtin")).hasValue() || ((ie.ucd.clops.runtime.options.FileOption)optionStore.getOptionByIdentifier("gen_docs_custom")).hasValue()) : false;
    }
  }
    
  public static class Rule3Expression implements Expression<List<String>> {
    /**
     * {@inheritDoc}
     */
    public List<String> evaluate(final OptionStore optionStore) {
      return Arrays.asList("You must specify the documentation type to generate.");
    }
  }
  
  public static class Rule4Condition implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(final OptionStore optionStore) {
      return ((ie.ucd.clops.runtime.options.StringEnumOption)optionStore.getOptionByIdentifier("gen_docs_builtin")).hasValue() ? !(((ie.ucd.clops.runtime.options.FileOption)optionStore.getOptionByIdentifier("gen_docs")).hasValue()) : false;
    }
  }
    
  public static class Rule4Expression implements Expression<List<String>> {
    /**
     * {@inheritDoc}
     */
    public List<String> evaluate(final OptionStore optionStore) {
      return Arrays.asList("--built-in cannot be used without --docs");
    }
  }
  
  public static class Rule5Condition implements Expression<Boolean> {
    /**
     * {@inheritDoc}
     */
    public Boolean evaluate(final OptionStore optionStore) {
      return ((ie.ucd.clops.runtime.options.FileOption)optionStore.getOptionByIdentifier("gen_docs_custom")).hasValue() ? !(((ie.ucd.clops.runtime.options.FileOption)optionStore.getOptionByIdentifier("gen_docs")).hasValue()) : false;
    }
  }
    
  public static class Rule5Expression implements Expression<List<String>> {
    /**
     * {@inheritDoc}
     */
    public List<String> evaluate(final OptionStore optionStore) {
      return Arrays.asList("--custom cannot be used without --docs");
    }
  }
  
}
