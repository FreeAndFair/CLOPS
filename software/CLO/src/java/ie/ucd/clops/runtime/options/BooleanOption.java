package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.parser.ProcessingResult;

/**
 * An option whose value is either true of false.
 *
 * @author Mikolas Janota
 * @author Fintan
 *
 */
public class BooleanOption extends BasicOption<Boolean> {
  private Boolean value;
  private boolean allowArg;

  //private static final String NO_ARG_SUFFIX = SEP_STRING;
  private static final String SUFFIX = "(=([^" + SEP + "]*))?" + SEP;
  
  
  public BooleanOption(String identifier, String prefix) {
    super(identifier, prefix);
    this.allowArg = true;
    setMatchingSuffix(SUFFIX);
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
   * @see ie.ucd.clo.runtime.options.Option#match(java.lang.String, int)
   */
  public ProcessingResult process() {
    String arg = match.group(3);
    if (arg == null) {
      try {
        set(true);
      } catch (InvalidOptionValueException e) {
        assert false;
      }
      return ProcessingResult.successfulProcess();
    } else {
      if (allowArg) {
        try {
          setFromString(arg);
          return ProcessingResult.successfulProcess();
        } catch (InvalidOptionValueException iove) {
          return ProcessingResult.erroneousProcess(iove.getMessage());
        }
      } else {
        return ProcessingResult.erroneousProcess("Option " + match.group(1) + " does not allow an argument.");
      }
    }
  }

  private boolean validValueString(String valueString) {
    return valueString.equalsIgnoreCase("true") || valueString.equalsIgnoreCase("false");
  }
  
  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#set(java.lang.Object)
   */
  public void set(Boolean value) throws InvalidOptionValueException {
    this.value = value;
  }

  @Override
  public Boolean convertStringToValue(String valueString) throws InvalidOptionValueException {
    if (valueString == null) {
      throw new InvalidOptionValueException("null provided as value.");
    }
    if (validValueString(valueString)) {
      return Boolean.valueOf(valueString);
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
      allowArg = Options.parseBooleanProperty(propertyName, propertyValue);
    } else {
      super.setProperty(propertyName, propertyValue);
    }
  }
  
  protected void setAllowArg(boolean allowArg) {
    this.allowArg = allowArg;
  }

}
