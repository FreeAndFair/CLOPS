package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.options.FileOption.FileOptionConstraints;

import java.io.File;

public class FileListOption extends ListOption<File> {

  private FileOptionConstraints constraints;
  
  public FileListOption(String identifier, String prefix) {
    super(identifier, prefix);
    setAllowDash(false);
    constraints = new FileOptionConstraints();
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

  @Override
  public boolean acceptsProperty(String propertyName) {
    return 
      constraints.acceptsProperty(propertyName) ||
      propertyName.equalsIgnoreCase("allowdash") ||
      super.acceptsProperty(propertyName);
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
