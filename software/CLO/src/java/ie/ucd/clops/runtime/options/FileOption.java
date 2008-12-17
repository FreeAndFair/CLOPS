package ie.ucd.clops.runtime.options;

import java.io.File;

/**
 * @author Fintan
 */
public class FileOption extends OneArgumentOption<File> {

  private FileOptionConstraints constraints;
  private File value;

  public FileOption(String identifier, String prefix) {
    super(identifier, prefix);
    setArgumentShape("[^-][^" + SEP + "]*");
    constraints = new FileOptionConstraints();
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#getValue()
   */
  public File getValue() { return value; }

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#hasValue()
   */
  public boolean hasValue() {
    return constraints != null;
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#set(java.lang.Object)
   */
  public void set(File value) throws InvalidOptionValueException {
    constraints.checkSetValue(value);
    this.value = value;	  
  }

  @Override
  public File convertStringToValue(String valueString) throws InvalidOptionValueException {
    if (valueString == null)
      throw new InvalidOptionValueException("Null File string.");
    return new File(valueString);
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#unset()
   */
  public void unset() {
    this.constraints = null;
  }

  @Override
  public boolean acceptsProperty(String propertyName) {
    if (constraints.acceptsProperty(propertyName)) {
      return true;
    } else {
      return super.acceptsProperty(propertyName);
    }
  }

  // TODO: Add "allowdash" property
  @Override
  public void setProperty(String propertyName, String propertyValue) throws InvalidOptionPropertyValueException {
    if (!constraints.setProperty(propertyName, propertyValue)) {
      super.setProperty(propertyName, propertyValue);
    }
  }

  @Override
  protected String getTypeString() {
    return "File";
  }

  public static class FileOptionConstraints {	  
    private boolean canExist;
    private boolean mustExist;
    private boolean canBeDir;
    private boolean mustBeDir;

    public FileOptionConstraints() {
      canExist = true;
      mustExist = false;
      canBeDir = true;
      mustBeDir = false;
    }

    public boolean acceptsProperty(String propertyName) {
      return    propertyName.equalsIgnoreCase("canexist") || propertyName.equalsIgnoreCase("mustexist") 
             || propertyName.equalsIgnoreCase("canBeDir") || propertyName.equalsIgnoreCase("mustBeDir") ;
    }

    public void checkSetValue(File file) throws InvalidOptionValueException {
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
    }

    public boolean canExist() {
      return canExist;
    }

    public void setCanExist(boolean canExist) {
      this.canExist = canExist;
      if (!canExist) {
        this.mustExist = false;
      }
    }

    public boolean mustExist() {
      return mustExist;
    }

    public void setMustExist(boolean mustExist) {
      this.mustExist = mustExist;
      if (mustExist) {
        this.canExist = true;
      }
    }

    public boolean canBeDir() {
      return canBeDir;
    }

    public void setCanBeDir(boolean canBeDir) {
      this.canBeDir = canBeDir;
      if (canBeDir) {
        this.canExist = true;
      } else {
        this.mustBeDir = false;
      }
    }

    public boolean mustBeDir() {
      return mustBeDir;
    }

    public void setMustBeDir(boolean mustBeDir) {
      this.mustBeDir = mustBeDir;
      if (mustBeDir) {
        this.canBeDir = true;
        this.canExist = true;
        this.mustExist = true;
      }
    }  

    public boolean setProperty(String propertyName, String propertyValue) throws InvalidOptionPropertyValueException {
      if (propertyName.equalsIgnoreCase("canexist")) {
        if (BooleanOption.validBooleanString(propertyValue)) {
          setCanExist(Boolean.parseBoolean(propertyValue));
          return true;
        } else {
          throw new InvalidOptionPropertyValueException("Invalid canexist, must be a boolean: " + propertyValue);
        }
      } else if (propertyName.equalsIgnoreCase("mustexist")) {
        if (BooleanOption.validBooleanString(propertyValue)) {
          setMustExist(Boolean.parseBoolean(propertyValue));
          return true;
        } else {
          throw new InvalidOptionPropertyValueException("Invalid canexist, must be a boolean: " + propertyValue);
        }      
      } else if (propertyName.equalsIgnoreCase("canbedir")) {
        if (BooleanOption.validBooleanString(propertyValue)) {
          setCanBeDir(Boolean.parseBoolean(propertyValue));
          return true;
        } else {
          throw new InvalidOptionPropertyValueException("Invalid canexist, must be a boolean: " + propertyValue);
        }      
      } else if (propertyName.equalsIgnoreCase("mustbedir")) {
        if (BooleanOption.validBooleanString(propertyValue)) {
          setMustBeDir(Boolean.parseBoolean(propertyValue));
          return true;
        } else {
          throw new InvalidOptionPropertyValueException("Invalid canexist, must be a boolean: " + propertyValue);
        }      
      }
      return false;
    }

  }

}
