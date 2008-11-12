package ie.ucd.clops.runtime.options;

import ie.ucd.clops.logging.CLOLogger;

import java.util.Set;
import java.util.logging.Level;

/**
 * 
 * @author Fintan
 *
 */
public class CountedBooleanOption extends BooleanOption {

  private int count;
  private int countMax;
  private boolean warnOnExceedingMax;
  private boolean errorOnExceedingMax;
  
  public CountedBooleanOption(String identifier, Set<String> aliases) {
    super(identifier, aliases);
    setAllowArg(false);
    count = 0;
    countMax = Integer.MAX_VALUE;
    warnOnExceedingMax = false;
    errorOnExceedingMax = false;
  }

  public CountedBooleanOption(String identifier) {
    super(identifier);
    setAllowArg(false);
    count = 0;
    countMax = Integer.MAX_VALUE;
    warnOnExceedingMax = false;
    errorOnExceedingMax = false;
  }

  @Override
  public void set(Object value) throws InvalidOptionValueException {
    if (value instanceof Boolean) {
      if ((Boolean)value) {
        if (count < countMax) {
          count++;
        } else {
          if (errorOnExceedingMax) {
            throw new InvalidOptionValueException("Too many usages of option " + this.getIdentifier());
          } else if (warnOnExceedingMax) {
            CLOLogger.getLogger().log(Level.WARNING, "Warning, used " + this.getIdentifier() + " too many times.");
          }
        }
      }
    }
    super.set(value);
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
      if (validBooleanString(propertyValue)) {
        warnOnExceedingMax = Boolean.parseBoolean(propertyValue);
      } else {
        throw new InvalidOptionPropertyValueException("Invalid warnonexceedingmax, must be a boolean: " + propertyValue);
      }      
    } else if (propertyName.equalsIgnoreCase("erroronexceedingmax")) {
      if (validBooleanString(propertyValue)) {
        errorOnExceedingMax = Boolean.parseBoolean(propertyValue);
      } else {
        throw new InvalidOptionPropertyValueException("Invalid erroronexceedingmax, must be a boolean: " + propertyValue);
      }      
    } else {
      super.setProperty(propertyName, propertyValue);
    }
  }
  
  public int getCount() {
    return count;
  }
  
  
}
