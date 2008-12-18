package ie.ucd.clops.runtime.rules;

import ie.ucd.clops.runtime.options.Option;
import ie.ucd.clops.runtime.options.OptionStore;

/**
 * 
 * @author Fintan
 * 
 */
public interface Expression<T> {

  /**
   * Evaluate this condition, using the option values from the provided OptionStore.
   * @param optionStore the OptionStore to be used in the evaluation.
   * @return a boolean indicating the result of evaluation.
   */
  public T evaluate(OptionStore optionStore);
  
  
  public static final Expression<Boolean> TRUE = new Expression<Boolean>() { public Boolean evaluate(OptionStore optionStore) { return true; } };
}
