package ie.ucd.clops.runtime.rules;

import ie.ucd.clops.logging.CLOLogger;
import ie.ucd.clops.runtime.options.InvalidOptionValueException;
import ie.ucd.clops.runtime.options.Option;
import ie.ucd.clops.runtime.options.OptionStore;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.logging.Level;

/**
 * 
 * @author Fintan
 *
 */
public class RuleStore {

  private final Map<String,List<FlyRule>> optionIdentifierToFlyRuleMap;
  //Other data structures for normal rules...
  private final List<OverrideRule> overrideRules;
    
  public RuleStore() {
    this.optionIdentifierToFlyRuleMap = new HashMap<String,List<FlyRule>>();
    this.overrideRules = new LinkedList<OverrideRule>();
  }
  
  public void addFlyRule(String optionIdentifier, FlyRule rule) {
    List<FlyRule> existingRules = optionIdentifierToFlyRuleMap.get(optionIdentifier);
    if (existingRules == null) {
      existingRules = new LinkedList<FlyRule>();
      optionIdentifierToFlyRuleMap.put(optionIdentifier, existingRules);
    }
    existingRules.add(rule);
    CLOLogger.getLogger().log(Level.FINE, "Added rule " + rule + " for " + optionIdentifier);
  }

  public List<FlyRule> getFlyRulesForOption(String optionIdentifier) {
    return optionIdentifierToFlyRuleMap.get(optionIdentifier);
  }

  public List<FlyRule> getFlyRulesForOption(Option<?> option) {
    return getFlyRulesForOption(option.getIdentifier());
  }
  
  public void applyFlyRules(Option<?> matchedOption, OptionStore optionStore) throws InvalidOptionValueException {
    List<FlyRule> rules = getFlyRulesForOption(matchedOption);
    if (rules != null) {
      CLOLogger.getLogger().log(Level.FINE, "Rules for " + matchedOption);
      for (FlyRule rule : rules) {
        CLOLogger.getLogger().log(Level.FINE, "Rule: " + rule);
        rule.applyRule(optionStore);
      }          
    }
  }
  
  public void applyOverrideRules(OptionStore optionStore) throws InvalidOptionValueException {
    for (OverrideRule rule : overrideRules) {
      rule.applyRule(optionStore);
    }
  }
  
}
