package ie.ucd.clops.runtime.options;

import java.util.Collection;
import java.util.LinkedList;


/**
 * @author Viliam Holub
 * @author Mikolas Janota
 * @author Fintan
 */
public class IntegerOption extends OneArgumentOption<Integer> {
	
	private Integer value;
	
	private boolean hasMaxValue;
	private boolean hasMinValue;
	private int maxValue;
	private int minValue;

	public IntegerOption(String identifier, String prefix) {
		super(identifier, prefix);
		this.hasMaxValue = false;
		this.hasMinValue = false;
		
		try {
      super.setProperty(ARGUMENTNAME, "<int>");
    } catch (InvalidOptionPropertyValueException e) {};
	}

	public Integer getRawValue() { return value; }

	/* (non-Javadoc)
	 * @see ie.ucd.clo.runtime.options.Option#set(java.lang.Object)
	 */
	public void set(Integer value) throws InvalidOptionValueException {
			Integer val = value;
			if (hasMaxValue && val > maxValue) {
				throw new InvalidOptionValueException(value + " is bigger than the maximum value, " + maxValue + ".");
			} else if (hasMinValue && val < minValue) {
				throw new InvalidOptionValueException(value + " is smaller than the minimum value, " + minValue + ".");
			} else {
				this.value = val;
			}
	}

	@Override
	public Integer convertStringToValue(String valueString) throws InvalidOptionValueException {
		if (valueString == null)
			throw new InvalidOptionValueException("Empty integer value.");
		try {
			return new Integer(valueString);
		} catch (NumberFormatException e) {
			throw new InvalidOptionValueException(valueString + " is not an integer number.", e);
		}
	}

	/* (non-Javadoc)
	 * @see ie.ucd.clo.runtime.options.Option#unset()
	 */
	public void unset() {
		this.value = null;
	}

	
	//Static for space/time efficiency (we don't need one per instance) 
	private static Collection<String> acceptedPropertyNames; 
	protected static Collection<String> getStaticAcceptedPropertyNames() {
		if (acceptedPropertyNames == null) {
			acceptedPropertyNames = new LinkedList<String>();	
			acceptedPropertyNames.addAll(OneArgumentOption.getStaticAcceptedPropertyNames());
			acceptedPropertyNames.add("maxvalue");
			acceptedPropertyNames.add("minvalue");
		}
		return acceptedPropertyNames;
	}
	
	@Override
	public Collection<String> getAcceptedPropertyNames() {
		return getStaticAcceptedPropertyNames();
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
				throw new InvalidOptionPropertyValueException("Invalid maxvalue, " + propertyValue + " is not an integer number.", e);
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
				throw new InvalidOptionPropertyValueException("Invalid minvalue, " + propertyValue + " is not an integer number.", e);
			}
			this.hasMinValue = true;
		} else {
			super.setProperty(propertyName, propertyValue);
		}
	}

	@Override
	protected String getTypeString() {
		return "Integer";
	}
	
	public int getIntegerValue() {
		return value;
	}
	
}
