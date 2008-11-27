package ie.ucd.clops.runtime.options;

import ie.ucd.clops.logging.CLOLogger;
import ie.ucd.clops.runtime.parser.ProcessingResult;

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

  @Override
  public boolean acceptsProperty(String propertyName) {
    if (   propertyName.equalsIgnoreCase("countstart") || propertyName.equalsIgnoreCase("countmax")
        || propertyName.equalsIgnoreCase("warnonexceedingmax") || propertyName.equalsIgnoreCase("erroronexceedingmax") ) {
      return true;
    } else {
      return super.acceptsProperty(propertyName);
    }
  }

  @Override
  public void setProperty(String propertyName, String propertyValue)
  throws InvalidOptionPropertyValueException {

    if (propertyName.equalsIgnoreCase("countstart")) {
      try {
        count = Integer.parseInt(propertyValue);
      } catch (NumberFormatException nfe) {
        throw new InvalidOptionPropertyValueException("Invalid countstart, " + propertyValue + " is not an integer.");
      }
    } else if (propertyName.equalsIgnoreCase("countmax")) {
      try {
        countMax = Integer.parseInt(propertyValue);
      } catch (NumberFormatException nfe) {
        throw new InvalidOptionPropertyValueException("Invalid countmax, " + propertyValue + " is not an integer.");
      }      
    } else if (propertyName.equalsIgnoreCase("warnonexceedingmax")) {
      if (BooleanOption.validBooleanString(propertyValue)) {
        warnOnExceedingMax = Boolean.parseBoolean(propertyValue);
      } else {
        throw new InvalidOptionPropertyValueException("Invalid warnonexceedingmax, must be a boolean: " + propertyValue);
      }      
    } else if (propertyName.equalsIgnoreCase("erroronexceedingmax")) {
      if (BooleanOption.validBooleanString(propertyValue)) {
        errorOnExceedingMax = Boolean.parseBoolean(propertyValue);
      } else {
        throw new InvalidOptionPropertyValueException("Invalid erroronexceedingmax, must be a boolean: " + propertyValue);
      }      
    } else {
      super.setProperty(propertyName, propertyValue);
    }
  }

  @Override
  protected String getTypeString() {
    return "Counted boolean.";
  }

  public Integer getValue() {
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

  public void setFromString(String value) throws InvalidOptionValueException {
    assert false;
  }

  public void unset() {
    assert false;
  }

  public int getCount() {
    return count;
  }


}
