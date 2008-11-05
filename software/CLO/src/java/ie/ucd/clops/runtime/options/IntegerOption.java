package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.parser.ProcessingResult;

import java.util.Set;

/**
 * @author Viliam Holub
 * @author Mikolas Janota
 * @author Fintan
 */
public class IntegerOption extends OneArgumentOption {
	
  private Integer value;
  
  private boolean hasMaxValue;
  private boolean hasMinValue;
  private int maxValue;
  private int minValue;

	public IntegerOption(String identifier, final Set<String> aliases) {
		super(identifier, aliases);
		this.hasMaxValue = false;
		this.hasMinValue = false;
	}

	public IntegerOption(String identifier) {
		super(identifier);
		this.hasMaxValue = false;
		this.hasMinValue = false;
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
	 * @see ie.ucd.clo.runtime.options.Option#set(java.lang.Object)
	 */
	public void set(Object value) throws InvalidOptionValueException {
		if (value instanceof Integer) {
		  Integer val = (Integer)value;
		  if (hasMaxValue && val > maxValue) {
		    throw new InvalidOptionValueException(value + " is bigger than the maximum value, " + maxValue + ".");
		  } else if (hasMinValue && val < minValue) {
		    throw new InvalidOptionValueException(value + " is smaller than the minimum value, " + minValue + ".");
		  } else {
		    this.value = val;
		  }
		} else {
			throw new InvalidOptionValueException(value + " is not an Integer.");
		}
	}

	public void setFromString(String valueString) throws InvalidOptionValueException {
		if (valueString == null)
			throw new InvalidOptionValueException("Empty integer value.");
		try {
			set(new Integer( valueString));
		} catch (NumberFormatException e) {
			throw new InvalidOptionValueException(valueString + " is not an integer number.");
		}		
	}

	/* (non-Javadoc)
	 * @see ie.ucd.clo.runtime.options.Option#unset()
	 */
	public void unset() {
		this.value = null;
	}

  @Override
  public boolean acceptsPropterty(String propertyName) {
    if (propertyName.equalsIgnoreCase("maxvalue") || propertyName.equalsIgnoreCase("minvalue")) {
      return true;
    } else {
      return super.acceptsPropterty(propertyName);
    }
  }

  @Override
  public void setProperty(String propertyName, String propertyValue) throws InvalidOptionPropertyValueException {
    if (propertyName.equalsIgnoreCase("maxvalue")) {
      try {
        this.maxValue = Integer.valueOf(propertyValue);
        if (hasMinValue && maxValue < minValue) {
          throw new InvalidOptionPropertyValueException("Invalid maxvalue, " + propertyValue + " is less than the minvalue (" + minValue + ").");
        } else {
          this.hasMaxValue = true;
        }
      } catch (NumberFormatException e) {
        throw new InvalidOptionPropertyValueException("Invalid maxvalue, " + propertyValue + " is not an integer number.");
      }
    } else if (propertyName.equalsIgnoreCase("minvalue")) {
      try {
        this.minValue = Integer.valueOf(propertyValue);
        if (hasMaxValue && maxValue < minValue) {
          throw new InvalidOptionPropertyValueException("Invalid minvalue, " + propertyValue + " is greater than the maxvalue (" + maxValue + ").");
        } else {
          this.hasMinValue = true;
        }
      } catch (NumberFormatException e) {
        throw new InvalidOptionPropertyValueException("Invalid minvalue, " + propertyValue + " is not an integer number.");
      }
      this.hasMinValue = true;
    }
    
    super.setProperty(propertyName, propertyValue);
  }

  @Override
  protected String getTypeString() {
    return "Integer";
  }
	
	public int getIntegerValue() {
	  return value;
	}
	
}
