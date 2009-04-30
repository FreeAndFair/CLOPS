package ie.ucd.clops.runtime.options;

import java.io.File;
import java.util.Collection;
import java.util.LinkedList;

/**
 * @author Fintan
 */
public class FileOption extends OneArgumentOption<File> {
  public static final String DASH_REGEXP = "[^" + SEP + "]+";
  public static final String NO_DASH_REGEXP = "[^-" + SEP + "][^" + SEP + "]*";

  private FileOptionConstraints constraints;
  private File value;

  public FileOption(String identifier, String prefix) {
    super(identifier, prefix);
    setArgumentShape(NO_DASH_REGEXP);
    constraints = new FileOptionConstraints();
    
    try {
      super.setProperty(ARGUMENTNAME, "<file>");
    } catch (InvalidOptionPropertyValueException e) {};
  }

  public File getRawValue() { return value; }

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

  //Static for space/time efficiency (we don't need one per instance) 
  private static Collection<String> acceptedPropertyNames; 
  protected static Collection<String> getStaticAcceptedPropertyNames() {
    if (acceptedPropertyNames == null) {
      acceptedPropertyNames = new LinkedList<String>();  
      acceptedPropertyNames.addAll(OneArgumentOption.getStaticAcceptedPropertyNames());
      acceptedPropertyNames.addAll(FileOptionConstraints.getStaticAcceptedPropertyNames());
      acceptedPropertyNames.add("allowdash");
    }
    return acceptedPropertyNames;
  }
  
  @Override
  public Collection<String> getAcceptedPropertyNames() {
    return getStaticAcceptedPropertyNames();
  }

  @Override
  public void setProperty(String propertyName, String propertyValue) throws InvalidOptionPropertyValueException {
    if (propertyName.equalsIgnoreCase("allowdash")) {
      if (Options.parseBooleanProperty(propertyName, propertyValue)) {
        setArgumentShape(DASH_REGEXP);
      } else {
        setArgumentShape(NO_DASH_REGEXP);
      }
    } else if (!constraints.setProperty(propertyName, propertyValue)) {
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
    
    //Static for space/time efficiency (we don't need one per instance) 
    private static Collection<String> acceptedPropertyNames; 
    protected static Collection<String> getStaticAcceptedPropertyNames() {
      if (acceptedPropertyNames == null) {
        acceptedPropertyNames = new LinkedList<String>();  
        acceptedPropertyNames.add("canexist");
        acceptedPropertyNames.add("mustexist");
        acceptedPropertyNames.add("canBeDir");
        acceptedPropertyNames.add("mustBeDir");
      }
      return acceptedPropertyNames;
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
        setCanExist(Options.parseBooleanProperty(propertyName, propertyValue));
      } else if (propertyName.equalsIgnoreCase("mustexist")) {
        setMustExist(Options.parseBooleanProperty(propertyName, propertyValue));
      } else if (propertyName.equalsIgnoreCase("canbedir")) {
        setCanBeDir(Options.parseBooleanProperty(propertyName, propertyValue));
      } else if (propertyName.equalsIgnoreCase("mustbedir")) {
        setMustBeDir(Options.parseBooleanProperty(propertyName, propertyValue));
      } else {
        return false;
      }
      return true;
    }

  }
 
  
}
