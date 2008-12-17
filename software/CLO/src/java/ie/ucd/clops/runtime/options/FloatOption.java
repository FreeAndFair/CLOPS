package ie.ucd.clops.runtime.options;


/**
 * @author Viliam Holub
 * @author Mikolas Janota
 * @author Fintan
 */
public class FloatOption extends OneArgumentOption<Float> {
	
  private Float value;
  
  private boolean hasMaxValue;
  private boolean hasMinValue;
  private float maxValue;
  private float minValue;

	public FloatOption(String identifier, String prefix) {
		super(identifier, prefix);
		this.hasMaxValue = false;
		this.hasMinValue = false;
	}

	/* (non-Javadoc)
	 * @see ie.ucd.clo.runtime.options.Option#getValue()
	 */
	public Float getValue() { return value; }

	/* (non-Javadoc)
	 * @see ie.ucd.clo.runtime.options.Option#hasValue()
	 */
	public boolean hasValue() {
		return value != null;
	}

	/* (non-Javadoc)
	 * @see ie.ucd.clo.runtime.options.Option#set(java.lang.Object)
	 */
	public void set(Float value) throws InvalidOptionValueException {
		  Float val = value;
		  if (hasMaxValue && val > maxValue) {
		    throw new InvalidOptionValueException(value + " is bigger than the maximum value, " + maxValue + ".");
		  } else if (hasMinValue && val < minValue) {
		    throw new InvalidOptionValueException(value + " is smaller than the minimum value, " + minValue + ".");
		  } else {
		    this.value = val;
		  }
	}

	@Override
  public Float convertStringToValue(String valueString) throws InvalidOptionValueException {
	  if (valueString == null)
      throw new InvalidOptionValueException("Empty float value.");
    try {
      return new Float(valueString);
    } catch (NumberFormatException e) {
      throw new InvalidOptionValueException(valueString + " is not a proper float number.", e);
    } 
  }

  /* (non-Javadoc)
	 * @see ie.ucd.clo.runtime.options.Option#unset()
	 */
	public void unset() {
		this.value = null;
	}

  @Override
  public boolean acceptsProperty(String propertyName) {
    if (propertyName.equalsIgnoreCase("maxvalue") || propertyName.equalsIgnoreCase("minvalue")) {
      return true;
    } else {
      return super.acceptsProperty(propertyName);
    }
  }

  @Override
  public void setProperty(String propertyName, String propertyValue) throws InvalidOptionPropertyValueException {
    if (propertyName.equalsIgnoreCase("maxvalue")) {
      try {
        this.maxValue = Float.valueOf(propertyValue);
        if (hasMinValue && maxValue < minValue) {
          throw new InvalidOptionPropertyValueException("Invalid maxvalue, " + propertyValue + " is less than the minvalue (" + minValue + ").");
        } else {
          this.hasMaxValue = true;
        }
      } catch (NumberFormatException e) {
        throw new InvalidOptionPropertyValueException("Invalid maxvalue, " + propertyValue + " is not a proper float number.", e);
      }
    } else if (propertyName.equalsIgnoreCase("minvalue")) {
      try {
        this.minValue = Float.valueOf(propertyValue);
        if (hasMaxValue && maxValue < minValue) {
          throw new InvalidOptionPropertyValueException("Invalid minvalue, " + propertyValue + " is greater than the maxvalue (" + maxValue + ").");
        } else {
          this.hasMinValue = true;
        }
      } catch (NumberFormatException e) {
        throw new InvalidOptionPropertyValueException("Invalid minvalue, " + propertyValue + " is not a proper float number.", e);
      }
      this.hasMinValue = true;
    }
    
    super.setProperty(propertyName, propertyValue);
  }

  @Override
  protected String getTypeString() {
    return "Float";
  }
	
	public float getFloatValue() {
	  return value;
	}
	
}
