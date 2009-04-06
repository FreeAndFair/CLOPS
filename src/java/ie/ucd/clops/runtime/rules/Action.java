package ie.ucd.clops.runtime.rules;

import ie.ucd.clops.runtime.options.InvalidOptionValueException;
import ie.ucd.clops.runtime.options.Option;
import ie.ucd.clops.runtime.options.OptionStore;

public class Action<T> {

  private final String optionId;
  private final Expression<T> expression;
  
  public Action(String optionId, Expression<T> expression) {
    this.optionId = optionId;
    this.expression = expression;
  }

  /**
   * Perform this action, modifying the specified Option in the provided OptionStore.
   * @param optionStore the OptionStore to use in performing this Action.
   */
  @SuppressWarnings("unchecked")
  public void perform(OptionStore optionStore) throws InvalidOptionValueException {
    Option<T> option = (Option<T>)optionStore.getOptionByIdentifier(optionId);
    T t = expression.evaluate(optionStore);
    option.set(t);
  }

  /*@pure*/public String getAffectedOption() {
      return optionId;
  }
  
}
