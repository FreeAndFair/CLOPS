package ie.ucd.clops.runtime.rules;

import ie.ucd.clops.logging.CLOLogger;
import ie.ucd.clops.runtime.errors.CLError;
import ie.ucd.clops.runtime.errors.InvalidOptionValueError;
import ie.ucd.clops.runtime.options.Option;
import ie.ucd.clops.runtime.options.OptionStore;
import ie.ucd.clops.runtime.options.exception.InvalidOptionValueException;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;
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

  public List<CLError> applyFlyRulesTraditional(Option<?> matchedOption, OptionStore optionStore) {
    List<CLError> errorList = new ArrayList<CLError>();
    List<FlyRule> rules = getFlyRulesForOption(matchedOption);
    if (rules != null) {
      CLOLogger.getLogger().log(Level.FINE, "Rules for " + matchedOption);
      for (FlyRule rule : rules) {
        CLOLogger.getLogger().log(Level.FINE, "Rule: " + rule);
        try {
          rule.applyRule(optionStore);
        } catch (InvalidOptionValueException e) {
          errorList.add(new InvalidOptionValueError(-1, e.getMessage()));
        }        
      }          
    }
    return errorList;
  }

  public List<CLError> applyFlyRules(Option<?> matchedOption, OptionStore optionStore) {
    if (shouldApplyFlyRulesTransitively()) {
      return applyFlyRulesTransitive(matchedOption, optionStore);      
    } else {
      return applyFlyRulesTraditional(matchedOption, optionStore);
    }
  }

  public List<CLError> applyFlyRulesTransitive(Option<?> matchedOption, OptionStore optionStore) {
    List<CLError> errorList = new ArrayList<CLError>();
    Set<Option<?>> triggers = new HashSet<Option<?>>(1);
    triggers.add(matchedOption); matchedOption=null;

    while (!triggers.isEmpty()) {
      Option<?> trigger = triggers.iterator().next();
      triggers.remove(trigger);

      CLOLogger.getLogger().log(Level.FINE, "FLY-rule trigger: " + trigger);

      List<FlyRule> rules = getFlyRulesForOption(trigger);
      if (rules != null) {
        for (FlyRule rule : rules) {
          CLOLogger.getLogger().log(Level.FINE, "Rule: " + rule);

          Map<String, Object> oldVals = getVals(optionStore, rule.getAffectedOptions());
          CLOLogger.getLogger().log(Level.FINE, "Affected opts: " + rule.getAffectedOptions());

          try {
            if (rule.applyRule(optionStore)) {
              for (String oId : rule.getAffectedOptions()) {
                Option<?> o = optionStore.getOptionByIdentifier(oId);
                if (!isSame(oldVals.get(oId), o.hasValue() ? o.getValue() : null)) {
                  triggers.add(o);
                } else {
                  CLOLogger.getLogger().log(Level.FINE, "Affected "  + o + " stayed the same");
                }
              }
            }
          } catch (InvalidOptionValueException e) {
            errorList.add(new InvalidOptionValueError(-1, e.getMessage()));
          }
        }          
      }
    }
    return errorList;
  }

  private static boolean isSame(Object o1, Object o2) {
    if (o1 == null) return o2 == null;
    if (o2 == null) return false;
    return o1.equals(o2);
  }

  private Map<String, Object> getVals(OptionStore optionStore, java.util.Collection<String> opts) {
    HashMap<String, Object> vals = new HashMap<String, Object>(opts.size());
    for (String oId : opts) {
      Option<?> o = optionStore.getOptionByIdentifier(oId);
      vals.put(oId, o.hasValue() ? o.getValue() : null);
    }
    return vals; 
  }

  public List<CLError> applyOverrideRules(OptionStore optionStore) {
    List<CLError> errorList = new ArrayList<CLError>();
    for (OverrideRule rule : overrideRules) {
      try {
        rule.applyRule(optionStore);
      } catch (InvalidOptionValueException e) {
        errorList.add(new InvalidOptionValueError(-1, e.getMessage()));
      } 
    }
    return errorList;
  }

  public void applyValidityRules(OptionStore optionStore) {
    try {
      for (ValidityRule rule : validityRules) {
        rule.applyRule(optionStore);
      }
    } catch (InvalidOptionValueException e) {
      assert false : "Validity rules do not modify option values!";
    }
  }

  /**
   * Should the fly rules be applied transitively?
   * @return
   */
  protected boolean shouldApplyFlyRulesTransitively() {
    return false;
  }
}
