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

import java.util.Set;
import java.util.HashSet;
/**
 * 
 * @author Fintan
 *
 */
public class RuleStore {
  public static boolean TRANSITIVE_FLYRULES  = false;

  private final Map<String,List<FlyRule>> optionIdentifierToFlyRuleMap;
  //Other data structures for normal rules...
  private final List<OverrideRule> overrideRules;
  private final List<ValidityRule> validityRules;
    
  public RuleStore() {
    this.optionIdentifierToFlyRuleMap = new HashMap<String,List<FlyRule>>();
    this.overrideRules = new LinkedList<OverrideRule>();
    this.validityRules = new LinkedList<ValidityRule>();
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
  
  public void addOverrideRule(OverrideRule rule) {
    overrideRules.add(rule);
  }

  public void addValidityRule(ValidityRule rule) {
    validityRules.add(rule);
  }
  
  public List<FlyRule> getFlyRulesForOption(String optionIdentifier) {
    return optionIdentifierToFlyRuleMap.get(optionIdentifier);
  }

  public List<FlyRule> getFlyRulesForOption(Option<?> option) {
    return getFlyRulesForOption(option.getIdentifier());
  }
  
  public void applyFlyRulesTraditional(Option<?> matchedOption, OptionStore optionStore) throws InvalidOptionValueException {
    List<FlyRule> rules = getFlyRulesForOption(matchedOption);
    if (rules != null) {
      CLOLogger.getLogger().log(Level.FINE, "Rules for " + matchedOption);
      for (FlyRule rule : rules) {
        CLOLogger.getLogger().log(Level.FINE, "Rule: " + rule);
        rule.applyRule(optionStore);
      }          
    }
  }

  public void applyFlyRules(Option<?> matchedOption, OptionStore optionStore) throws InvalidOptionValueException {
    if (TRANSITIVE_FLYRULES) {
      applyFlyRulesTransitive(matchedOption, optionStore);      
    }
    else {
      applyFlyRulesTraditional(matchedOption, optionStore);
    }
  }

  public void applyFlyRulesTransitive(Option<?> matchedOption, OptionStore optionStore) throws InvalidOptionValueException {
    Set<Option> triggers = new HashSet<Option>(1);
    triggers.add(matchedOption); matchedOption=null;

    while (!triggers.isEmpty()) {
      Option trigger = triggers.iterator().next();
      triggers.remove(trigger);

      CLOLogger.getLogger().log(Level.FINE, "FLY-rule trigger: " + trigger);

      List<FlyRule> rules = getFlyRulesForOption(trigger);
      if (rules != null) {
        for (FlyRule rule : rules) {
          CLOLogger.getLogger().log(Level.FINE, "Rule: " + rule);

          Map<String, Object> oldVals = getVals(optionStore, rule.getAffectedOptions());
          CLOLogger.getLogger().log(Level.FINE, "Affected opts: " + rule.getAffectedOptions());

          if (rule.applyRule(optionStore)) {
            for (String oId : rule.getAffectedOptions()) {
              Option o = optionStore.getOptionByIdentifier(oId);
              if (!isSame(oldVals.get(oId), o.hasValue() ? o.getValue() : null)) {
                triggers.add(o);
              } else {
                CLOLogger.getLogger().log(Level.FINE, "Affected "  + o + " stayed the same");
              }
            }
          }
        }          
      }
    }
  }

  private static boolean isSame(Object o1, Object o2) {
    if (o1 == null) return o2 == null;
    if (o2 == null) return false;
    return o1.equals(o2);
  }

  private Map<String, Object> getVals(OptionStore optionStore, java.util.Collection<String> opts) {
    HashMap<String, Object> vals = new HashMap<String, Object>(opts.size());
    for (String oId : opts) {
      Option o = optionStore.getOptionByIdentifier(oId);
      vals.put(oId, o.hasValue() ? o.getValue() : null);
    }
    return vals; 
  }
  
  public void applyOverrideRules(OptionStore optionStore) throws InvalidOptionValueException {
    for (OverrideRule rule : overrideRules) {
      rule.applyRule(optionStore);
    }
  }
  
  public void applyValidityRules(OptionStore optionStore) throws InvalidOptionValueException {
    for (ValidityRule rule : validityRules) {
      rule.applyRule(optionStore);
    }
  }
  
}
