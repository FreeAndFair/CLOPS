package ie.ucd.clops.runtime.options;


/**
 * @author Fintan
 */
public class StringOption extends OneArgumentOption<String> {
	
  private String value;
  private boolean stripquotes;

	public StringOption(String identifier, String prefix) {
		super(identifier, prefix);
		this.stripquotes = false;
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
	public void set(String value) throws InvalidOptionValueException {
	  if (stripquotes) {
	    this.value = stripQuotesIfNecessary(value);
	  } else {
	    this.value = value;
	  }
	}
	
	private String stripQuotesIfNecessary(String value) {
	  if (value.length() >=2 && 
        value.charAt(0) == '"' && 
        value.charAt(value.length()-1) == '"') {
      return value.substring(1, value.length()-1);
	  } else {
	    return value;
	  }
	}

	@Override
  public String convertStringToValue(String valueString) throws InvalidOptionValueException {
	  if (valueString == null)
      throw new InvalidOptionValueException("Null String.");
	  return valueString;
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

  @Override
  public boolean acceptsProperty(String propertyName) {
    return propertyName.equalsIgnoreCase("stripquotesifpresent") || super.acceptsProperty(propertyName);
  }

  @Override
  public void setProperty(String propertyName, String propertyValue)
      throws InvalidOptionPropertyValueException {
    if (propertyName.equalsIgnoreCase("stripquotesifpresent")) {
      if (BooleanOption.validBooleanString(propertyValue)) {
        stripquotes = Boolean.parseBoolean(propertyValue);
      } else {
        throw new InvalidOptionPropertyValueException("Invalid stripquotesifpresent, must be a boolean: " + propertyValue);
      }
    } else {
      super.setProperty(propertyName, propertyValue);
    }
  }
	
	
	
}
