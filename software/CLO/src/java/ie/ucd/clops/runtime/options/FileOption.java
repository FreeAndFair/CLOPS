package ie.ucd.clops.runtime.options;

import java.io.File;
import java.util.Set;

/**
 * @author Fintan
 */
public class FileOption extends OneArgumentOption {
	
  private File value;
  
  private boolean canExist;
  private boolean mustExist;
  private boolean canBeDir;
  private boolean mustBeDir;

	public FileOption(String identifier, final Set<String> aliases) {
		super(identifier, aliases);
		canExist = true;
	  mustExist = false;
	  canBeDir = true;
	  mustBeDir = false;
	}

	public FileOption(String identifier) {
		super(identifier);
		canExist = true;
    mustExist = false;
    canBeDir = true;
    mustBeDir = false;
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
		if (value instanceof File) {
		  File file = (File)value;
		  
		  //Check existence properties
		  if (file.exists()) {
		    if (!canExist) {
		      throw new InvalidOptionValueException("File cannot exist: " + file.getPath());
		    }
		  } else {
		    if (mustExist) {
		      throw new InvalidOptionValueException("File must exist: " + file.getPath());
		    }
		  }
		  
		  //Check directory properties
		  if (file.isDirectory()) {
		    if (!canBeDir) {
		      throw new InvalidOptionValueException("File cannot be a directory: " + file.getPath());
		    }
		  } else {
		    if (mustBeDir) {
		      throw new InvalidOptionValueException("File must be a directory: " + file.getPath());
		    }
		  }
		  
		  this.value = file;
		} else {
			throw new InvalidOptionValueException(value + " is not a File.");
		}
	}

	public void setFromString(String valueString) throws InvalidOptionValueException {
		if (valueString == null)
			throw new InvalidOptionValueException("Null File string.");
		set(new File(valueString));
	}

	/* (non-Javadoc)
	 * @see ie.ucd.clo.runtime.options.Option#unset()
	 */
	public void unset() {
		this.value = null;
	}

  @Override
  public boolean acceptsProperty(String propertyName) {
    if (   propertyName.equalsIgnoreCase("canexist") || propertyName.equalsIgnoreCase("mustexist") 
        || propertyName.equalsIgnoreCase("canBeDir") || propertyName.equalsIgnoreCase("mustBeDir") ) {
      return true;
    } else {
      return super.acceptsProperty(propertyName);
    }
  }

  @Override
  public void setProperty(String propertyName, String propertyValue) throws InvalidOptionPropertyValueException {
    if (propertyName.equalsIgnoreCase("canexist")) {
      if (validBooleanString(propertyValue)) {
        canExist = Boolean.parseBoolean(propertyValue);
        if (!canExist) {
          mustExist = false;
        }
      } else {
        throw new InvalidOptionPropertyValueException("Invalid canexist, must be a boolean: " + propertyValue);
      }
    } else if (propertyName.equalsIgnoreCase("mustexist")) {
      if (validBooleanString(propertyValue)) {
        mustExist = Boolean.parseBoolean(propertyValue);
        if (mustExist) {
          canExist = true;
        }
      } else {
        throw new InvalidOptionPropertyValueException("Invalid canexist, must be a boolean: " + propertyValue);
      }      
    } else if (propertyName.equalsIgnoreCase("canbedir")) {
      if (validBooleanString(propertyValue)) {
        canBeDir = Boolean.parseBoolean(propertyValue);
        if (canBeDir) {
          canExist = true;
        } else {
          mustBeDir = false;
        }
      } else {
        throw new InvalidOptionPropertyValueException("Invalid canexist, must be a boolean: " + propertyValue);
      }      
    } else if (propertyName.equalsIgnoreCase("mustbedir")) {
      if (validBooleanString(propertyValue)) {
        mustBeDir = Boolean.parseBoolean(propertyValue);
        if (mustBeDir) {
          canBeDir = true;
          canExist = true;
          mustExist = true;
        }
      } else {
        throw new InvalidOptionPropertyValueException("Invalid canexist, must be a boolean: " + propertyValue);
      }      
    } else {
      super.setProperty(propertyName, propertyValue);
    }
  }
  
  private boolean validBooleanString(String s) {
    return s.equalsIgnoreCase("true") || s.equalsIgnoreCase("false");
  }

  @Override
  protected String getTypeString() {
    return "File";
  }
	
	public File getFileValue() {
	  return value;
	}
	
}
