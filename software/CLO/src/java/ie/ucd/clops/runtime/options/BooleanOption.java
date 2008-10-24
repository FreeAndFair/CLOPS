/**
 * 
 */
package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.parser.ProcessingResult;

import java.util.Set;

/**
 * @author Mikolas Janota
 *
 */
public class BooleanOption extends BasicOption {
  private Boolean value;

  public BooleanOption(String identifier, final Set<String> aliases) {
    super(identifier, aliases);
  }

  public BooleanOption(String identifier) {
    super(identifier);
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#getType()
   */
  public  OptionType getType() { return OptionType.BOOLEAN; }

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#getValue()
   */
  public Object getValue() { return value; }

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#hasValue()
   */
  public boolean hasValue() {
    return value != null;
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#match(java.lang.String[], int)
   */
  public ProcessingResult process(String[] args, int offset) {
    String currentArg = args[offset];
    if (getAliases().contains(currentArg)) {
      this.value = true;
      return new ProcessingResult(1, false, null);
    } else {
      return null;
    }
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#set(java.lang.Object)
   */
  public void set(Object value) {
    this.value = (Boolean)value;
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#unset()
   */
  public void unset() {
    this.value = null;
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.IMatchable#getMatchingOption(java.lang.String)
   */  
  public Option getMatchingOption(String argument) {
    return getAliases().contains(argument) ? this : null;
  }

  @Override
  public String toString() {
    return "Boolean Option: \"" + getIdentifier() + "\"";
  }



}
