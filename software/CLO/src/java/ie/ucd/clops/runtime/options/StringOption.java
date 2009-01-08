package ie.ucd.clops.runtime.options;

import java.util.Collection;
import java.util.LinkedList;


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

  //Static for space/time efficiency (we don't need one per instance) 
  private static Collection<String> acceptedPropertyNames; 
  protected static Collection<String> getStaticAcceptedPropertyNames() {
    if (acceptedPropertyNames == null) {
      acceptedPropertyNames = new LinkedList<String>();  
      acceptedPropertyNames.addAll(OneArgumentOption.getStaticAcceptedPropertyNames());
      acceptedPropertyNames.add("stripquotesifpresent");
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
    if (propertyName.equalsIgnoreCase("stripquotesifpresent")) {
      stripquotes = Options.parseBooleanProperty(propertyName, propertyValue);
    } else {
      super.setProperty(propertyName, propertyValue);
    }
  }
	
	
	
}
