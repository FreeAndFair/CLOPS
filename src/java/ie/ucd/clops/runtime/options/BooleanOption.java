package ie.ucd.clops.runtime.options;

import java.util.Collection;
import java.util.LinkedList;

import ie.ucd.clops.runtime.parser.ProcessingResult;

/**
 * An option whose value is either true of false.
 *
 * @author Mikolas Janota
 * @author Fintan
 *
 *
 */
// TODO(rgrig): Why doesn't this inherit from OneArgumentOption?
public class BooleanOption extends BasicOption<Boolean> {
  private static final String ALLOWARG = "allowarg";

  private Boolean value;
  private boolean allowArg;

  private static final String NO_ARG_SUFFIX = "" + SEP;
  private static final String SUFFIX = "(=([^" + SEP + "]*))?" + SEP;
  
  
  public BooleanOption(String identifier, String prefix) {
    super(identifier, prefix);
    this.allowArg = true;
    setMatchingSuffix(SUFFIX);
    
  }

  public Boolean getRawValue() { return value; }

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#match(java.lang.String, int)
   */
  public ProcessingResult process() {
    String arg = match.groupCount() >= 3 ? match.group(3) : null;
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
        return ProcessingResult.erroneousProcess("Option " + match.group(1) + " does not allow an argument, which is '" + arg + "'.");
      }
    }
  }

  public String getMatchingValueString() {
    return match.groupCount() >= 3? match.group(3) : null;
  }

  private boolean validValueString(String valueString) {
    return 
      allowArg ? valueString.equalsIgnoreCase("true") || valueString.equalsIgnoreCase("false")
               : valueString=="";


  }
  
  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#set(java.lang.Object)
   */
  public void set(Boolean value) throws InvalidOptionValueException {
    this.value = value;
  }

  @Override
  public Boolean convertStringToValue(String valueString) throws InvalidOptionValueException {
    if (!allowArg) {
      if (valueString != null) throw new InvalidOptionValueException("No argument allowed.");
      else return new Boolean(true);
    } else {
      if (valueString == null) valueString = "true";
      if (validValueString(valueString)) {
        return Boolean.valueOf(valueString);
      } else {
        throw new InvalidOptionValueException(valueString + " is not a boolean string.");
      }    
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

  //Static for space/time efficiency (we don't need one per instance) 
  private static Collection<String> acceptedPropertyNames; 
  protected static Collection<String> getStaticAcceptedPropertyNames() {
    if (acceptedPropertyNames == null) {
      acceptedPropertyNames = new LinkedList<String>();  
      acceptedPropertyNames.addAll(BasicOption.getStaticAcceptedPropertyNames());
      acceptedPropertyNames.add(ALLOWARG);
    }
    return acceptedPropertyNames;
  }
  
  @Override
  public Collection<String> getAcceptedPropertyNames() {
    return getStaticAcceptedPropertyNames();
  }

  @Override
  public void setProperty(String propertyName, String propertyValue)
      throws InvalidOptionPropertyValueException {
    if (propertyName.equalsIgnoreCase(ALLOWARG)) {
      setAllowArg(Options.parseBooleanProperty(propertyName, propertyValue));
    } else {
      super.setProperty(propertyName, propertyValue);
    }
  }

  /** Set {@code this.allowArg} to a given value and adapts the regex
   * suffix accordingly. 
   * @param allowArg the new value for {@code this.allowArg}
   **/
  protected void setAllowArg(boolean allowArg) {
    this.allowArg=allowArg;
    setMatchingSuffix(allowArg ? SUFFIX : NO_ARG_SUFFIX);
  }

}
