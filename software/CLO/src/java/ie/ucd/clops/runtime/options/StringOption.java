package ie.ucd.clops.runtime.options;

import java.util.Set;

/**
 * @author Fintan
 */
public class StringOption extends OneArgumentOption<String> {
	
  private String value;

	public StringOption(String identifier, final Set<String> aliases) {
		super(identifier, aliases);
	}

	public StringOption(String identifier) {
		super(identifier);
	}

	/* (non-Javadoc)
	 * @see ie.ucd.clo.runtime.options.Option#getValue()
	 */
	public String getValue() { return value; }

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
		if (value instanceof String) {
		  this.value = (String)value;
		} else {
			throw new InvalidOptionValueException(value + " is not a String.");
		}
	}

	public void setFromString(String valueString) throws InvalidOptionValueException {
		if (valueString == null)
			throw new InvalidOptionValueException("Null String.");
		set(valueString);		
	}

	/* (non-Javadoc)
	 * @see ie.ucd.clo.runtime.options.Option#unset()
	 */
	public void unset() {
		this.value = null;
	}

  @Override
  protected String getTypeString() {
    return "String";
  }
	
	public String getStringValue() {
	  return value;
	}
	
}
