package ie.ucd.clops.runtime.options;

import java.util.Collection;
import java.util.LinkedList;

import ie.ucd.clops.runtime.parser.ProcessingResult;

/**
 * Option that requires one argument.
 * Either -op1=value or ... -op1 value ...
 * 
 * @author Fintan
 *
 */
public abstract class OneArgumentOption<T> extends BasicOption<T> {

  private String between = "[=" + SEP + "]";
  private String argumentShape = "[^" + SEP + "]*";
  
  public OneArgumentOption(String identifier, String prefix) {
    super(identifier, prefix);
    updateSuffix();
  }

  //Static for space/time efficiency (we don't need one per instance) 
  private static Collection<String> acceptedPropertyNames; 
  protected static Collection<String> getStaticAcceptedPropertyNames() {
    if (acceptedPropertyNames == null) {
      acceptedPropertyNames = new LinkedList<String>();  
      acceptedPropertyNames.addAll(BasicOption.getStaticAcceptedPropertyNames());
      acceptedPropertyNames.add("between");
      acceptedPropertyNames.add("argumentshape");
    }
    return acceptedPropertyNames;
  }
  
  @Override
  public Collection<String> getAcceptedPropertyNames() {
    return getStaticAcceptedPropertyNames();
  }

  @Override
  public void setProperty(String propertyName, String propertyValue) throws InvalidOptionPropertyValueException {
    if (propertyName.equalsIgnoreCase("between")) {
      setBetween(propertyValue);
    } else if (propertyName.equalsIgnoreCase("argumentshape")) {
      setArgumentShape(propertyValue);
    } else {
      super.setProperty(propertyName, propertyValue);
    }
  }

  public void setBetween(String newBetween) {
    between = BasicOption.sanitizePrefix(newBetween);
    updateSuffix();
  }

  public void setArgumentShape(String newArgumentShape) {
    argumentShape = newArgumentShape;
    updateSuffix();
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#match(java.lang.String, int)
   */
  public ProcessingResult process() {
    String arg = match.group(2);
    if (arg == null || arg.equals("")) {
      return ProcessingResult.erroneousProcess( "Parameter expected for "
        + match.group(0));
    } else {
      try {
        setFromString(arg);
        return ProcessingResult.successfulProcess();
      } catch (InvalidOptionValueException iove) {
        return ProcessingResult.erroneousProcess(iove.getMessage());
      }
    }
  }

  private void updateSuffix() {
    setMatchingSuffix(
      "(?:" + between + "(" + argumentShape + "))?" + SEP);
  }
}
