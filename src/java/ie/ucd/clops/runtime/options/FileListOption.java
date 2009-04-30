package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.options.FileOption.FileOptionConstraints;

import java.io.File;
import java.util.Collection;
import java.util.LinkedList;

public class FileListOption extends ListOption<File> {

  private FileOptionConstraints constraints;
  
  public FileListOption(String identifier, String prefix) {
    super(identifier, prefix);
    setAllowDash(false);
    constraints = new FileOptionConstraints();
    
    try {
      super.setProperty(ARGUMENTNAME, "<file>");
    } catch (InvalidOptionPropertyValueException e) {};
  }

  @Override
  public File convertFromStringToListValue(String valueString) throws InvalidOptionValueException {
    File file = new File(valueString);
    constraints.checkSetValue(file);
    return file;
  }

  @Override
  protected String getTypeString() {
    return "File list";
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
      setAllowDash(Options.parseBooleanProperty(propertyName, propertyValue));
    } else if (!constraints.setProperty(propertyName, propertyValue)) {
      super.setProperty(propertyName, propertyValue);
    }
  }

  private void setAllowDash(boolean allowDash) {
    String fileRegex = allowDash ? FileOption.DASH_REGEXP : FileOption.NO_DASH_REGEXP;
    setArgumentShape(fileRegex + "(" + splittingString + fileRegex + ")*");
  }
}
