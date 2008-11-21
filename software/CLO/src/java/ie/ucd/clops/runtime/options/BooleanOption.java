package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.parser.ProcessingResult;

import java.util.Set;

/**
 * @author Mikolas Janota
 * @author Fintan
 *
 */
public class BooleanOption extends BasicOption<Boolean> {
  private Boolean value;
  private boolean allowArg;
  
  public BooleanOption(String identifier, final Set<String> aliases) {
    super(identifier, aliases);
    this.allowArg = true;
  }

  public BooleanOption(String identifier) {
    super(identifier);
    this.allowArg = true;
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#getValue()
   */
  public Boolean getValue() { return value; }

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
    if (allowArg) {
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
        try { set(Boolean.TRUE); } catch (InvalidOptionValueException iove) { assert false; }
        return ProcessingResult.successfulProcess(1);
      }
    } else {
      if (currentArg.length() > alias.length() && currentArg.charAt(alias.length()) == '=') {
        return ProcessingResult.erroneousProcess("Option " + alias + " does not allow an argument.");
      } else {
        //It's true...
        try { set(Boolean.TRUE); } catch (InvalidOptionValueException iove) { assert false; }
        return ProcessingResult.successfulProcess(1);
      }
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

  public boolean getBooleanValue() {
    return value;
  }

  @Override
  public boolean acceptsProperty(String propertyName) {
    if (propertyName.equalsIgnoreCase("allowarg")) {
      return true;
    } else {
      return super.acceptsProperty(propertyName);
    }
  }

  @Override
  public void setProperty(String propertyName, String propertyValue)
      throws InvalidOptionPropertyValueException {
    if (propertyName.equalsIgnoreCase("allowarg")) {
      if (validBooleanString(propertyValue)) {
        allowArg = Boolean.parseBoolean(propertyValue);
      } else {
        throw new InvalidOptionPropertyValueException("Invalid allowarg, must be a boolean: " + propertyValue);
      }
    } else {
      super.setProperty(propertyName, propertyValue);
    }
  }
  
  public static boolean validBooleanString(String s) {
    return s.equalsIgnoreCase("true") || s.equalsIgnoreCase("false");
  } 
  
  protected void setAllowArg(boolean allowArg) {
    this.allowArg = allowArg;
  }

}
