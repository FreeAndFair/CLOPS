package ie.ucd.clops.runtime.options;

import ie.ucd.clops.logging.CLOLogger;
import ie.ucd.clops.runtime.parser.ProcessingResult;

import java.util.Collection;
import java.util.LinkedList;
import java.util.logging.Level;

/**
 * 
 * @author Fintan
 *
 */
public class CountedBooleanOption extends BasicOption<Integer> {

  private static final String SUFFIX = "(=([^" + SEP + "]*))?" + SEP;

  private int count;
  private int countMax;
  private boolean warnOnExceedingMax;
  private boolean errorOnExceedingMax;

  public CountedBooleanOption(String identifier, String prefix) {
    super(identifier, prefix);

    setMatchingSuffix(SUFFIX);

    count = 0;
    countMax = Integer.MAX_VALUE;
    warnOnExceedingMax = false;
    errorOnExceedingMax = false;
  }

  //Static for space/time efficiency (we don't need one per instance) 
  private static Collection<String> acceptedPropertyNames; 
  protected static Collection<String> getStaticAcceptedPropertyNames() {
    if (acceptedPropertyNames == null) {
      acceptedPropertyNames = new LinkedList<String>();  
      acceptedPropertyNames.addAll(BasicOption.getStaticAcceptedPropertyNames());
      acceptedPropertyNames.add("countstart");
      acceptedPropertyNames.add("countmax");
      acceptedPropertyNames.add("warnonexceedingmax");
      acceptedPropertyNames.add("erroronexceedingmax");
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

    if (propertyName.equalsIgnoreCase("countstart")) {
      try {
        count = Integer.parseInt(propertyValue);
      } catch (NumberFormatException nfe) {
        throw new InvalidOptionPropertyValueException("Invalid countstart, " + propertyValue + " is not an integer.", nfe);
      }
    } else if (propertyName.equalsIgnoreCase("countmax")) {
      try {
        countMax = Integer.parseInt(propertyValue);
      } catch (NumberFormatException nfe) {
        throw new InvalidOptionPropertyValueException("Invalid countmax, " + propertyValue + " is not an integer.", nfe);
      }      
    } else if (propertyName.equalsIgnoreCase("warnonexceedingmax")) {
      warnOnExceedingMax = Options.parseBooleanProperty(propertyName, propertyValue);
    } else if (propertyName.equalsIgnoreCase("erroronexceedingmax")) {
      errorOnExceedingMax = Options.parseBooleanProperty(propertyName, propertyValue);
    } else {
      super.setProperty(propertyName, propertyValue);
    }
  }

  @Override
  protected String getTypeString() {
    return "Counted boolean.";
  }

  public Integer getRawValue() {
    return count;
  }

  public ProcessingResult process() {
    String arg = match.group(3);
    if (arg == null) {
      try { 
        set(count+1);
        return ProcessingResult.successfulProcess();
      } catch (InvalidOptionValueException e) {
        return ProcessingResult.erroneousProcess(e.getMessage());
      }      
    } else {
      return ProcessingResult.erroneousProcess("Option " + match.group(1) + " does not allow an argument.");
    }
  }

  public String getMatchingValueString() {
    return match.group(3);
  }

  public void set(Integer value) throws InvalidOptionValueException {
    if (value > countMax) {
      if (errorOnExceedingMax) {
        throw new InvalidOptionValueException("Too many usages of option " + this.getIdentifier());
      } else if (warnOnExceedingMax) {
        CLOLogger.getLogger().log(Level.WARNING, "Warning, used " + this.getIdentifier() + " too many times.");
      }
    } else {
      count = value;
    }
  }

  @Override
  public Integer convertStringToValue(String value) throws InvalidOptionValueException {
    if (value == null)
      throw new InvalidOptionValueException("Empty integer value.");
    try {
      return new Integer(value);
    } catch (NumberFormatException e) {
      throw new InvalidOptionValueException(value + " is not an integer number.", e);
    }
  }

  public void unset() {
    // TODO(rg): I think this should be an exception.
    assert false;
  }

  public int getCount() {
    return count;
  }


}
