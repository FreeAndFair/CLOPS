package ie.ucd.clops.runtime.rules;

import ie.ucd.clops.runtime.options.InvalidOptionValueException;
import ie.ucd.clops.runtime.options.OptionStore;

import java.util.LinkedList;
import java.util.List;

/**
 * 
 * @author Fintan
 *
 */
public abstract class Rule {

  private final Trigger trigger;
  private final Expression<Boolean> condition;
  private final List<Action<?>> actions;
  
  public Rule(Trigger trigger, Expression<Boolean> condition) {
    this.trigger = trigger;
    this.condition = condition;
    this.actions = new LinkedList<Action<?>>();
  }
  
  public void addAction(Action<?> action) {
    this.actions.add(action);
  }  
  
  public Trigger getTrigger() {
    return trigger;
  }

  /** Apply this rule to the given option store.
   *@param optionStore the option store on which evaluate the condition and to affect
   *@return true iff the rule fired
   */
  public boolean applyRule(OptionStore optionStore) throws InvalidOptionValueException {
    if (condition.evaluate(optionStore)) {
      for (Action<?> action : actions) {
        action.perform(optionStore);
      }
      return true;
    } else {
      return false;
    }
  }

  /** Returns a list of options that get affected by this rule, if fired. */
  public java.util.Set<String> getAffectedOptions() {
       java.util.Set<String> retv = new java.util.HashSet<String>(actions.size());
       for (Action<?> a : actions) retv.add(a.getAffectedOption());
       return retv;
   }  
}
