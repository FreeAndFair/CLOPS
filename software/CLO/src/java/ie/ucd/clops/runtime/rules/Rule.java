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
  
  public void applyRule(OptionStore optionStore) throws InvalidOptionValueException {
    if (condition.evaluate(optionStore)) {
      for (Action<?> action : actions) {
        action.perform(optionStore);
      }
    }
  }
  
}
