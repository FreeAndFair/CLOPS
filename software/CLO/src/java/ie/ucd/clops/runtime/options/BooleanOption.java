package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.parser.ProcessingResult;

import java.util.Set;

/**
 * @author Mikolas Janota
 * @author Fintan
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
    assert this.getMatchingOption(currentArg) == this;
    String alias = getMatchingAlias(currentArg);
    //If we allow -arg=VALUE
    if (currentArg.length() > alias.length() && currentArg.charAt(alias.length()) == '=') {
      String suffix = currentArg.substring(alias.length() + 1);
      try {
        setFromString(suffix);
        return ProcessingResult.successfulProcess(1);
      } catch (InvalidOptionValueException iove) {
        return ProcessingResult.erroneousProcess(iove.getMessage());
      }
    } else {
      //It's true...
      this.value = Boolean.TRUE;
      return ProcessingResult.successfulProcess(1);
    }
  }

  private boolean validValueString(String valueString) {
    return valueString.equalsIgnoreCase("true") || valueString.equalsIgnoreCase("false");
  }
  
  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#set(java.lang.Object)
   */
  public void set(Object value) throws InvalidOptionValueException {
    if (value instanceof Boolean) {
      this.value = (Boolean)value;
    } else {
      throw new InvalidOptionValueException(value + " is not a Boolean.");
    }
  }

  public void setFromString(String valueString) throws InvalidOptionValueException {
    if (valueString == null) {
      throw new InvalidOptionValueException("null provided as value.");
    }
    if (validValueString(valueString)) {
      set(Boolean.valueOf(valueString));
    } else {
      throw new InvalidOptionValueException(valueString + " is not a boolean string.");
    }    
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#unset()
   */
  public void unset() {
    this.value = null;
  }

  @Override
  protected String getTypeString() {
    return "Boolean";
  }

    

}
