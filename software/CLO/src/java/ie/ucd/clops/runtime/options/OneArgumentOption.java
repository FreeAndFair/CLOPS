package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.parser.ProcessingResult;

/**
 * Option that requires one argument.
 * Either -op1=value or ... -op1 value ...
 * 
 * @author Fintan
 *
 */
public abstract class OneArgumentOption<T> extends BasicOption<T> {

  private static final String BETWEEN = "[=" + SEP + "]";
  private static final String SUFFIX = "([^" + SEP + "]*)" + SEP;
  
  public OneArgumentOption(String identifier, String prefix) {
    super(identifier, prefix);
    setMatchingSuffix(BETWEEN + SUFFIX);
  }

  @Override
  public boolean acceptsProperty(String propertyName) {
    return propertyName.equals("between") 
      || super.acceptsProperty(propertyName);
  }

  @Override
  public void setProperty(String propertyName, String propertyValue) throws InvalidOptionPropertyValueException {
    if (propertyName.equals("between")) {
      setMatchingSuffix(propertyValue + SUFFIX);
    } else {
      super.setProperty(propertyName, propertyValue);
    }
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#match(java.lang.String, int)
   */
  public ProcessingResult process() {
    String arg = match.group(2);
    if (arg.equals("")) {
      return ProcessingResult.erroneousProcess( "Parameter expected");
    } else {
      try {
        setFromString(arg);
        return ProcessingResult.successfulProcess();
      } catch (InvalidOptionValueException iove) {
        return ProcessingResult.erroneousProcess(iove.getMessage());
      }
    }
  }
  
}
