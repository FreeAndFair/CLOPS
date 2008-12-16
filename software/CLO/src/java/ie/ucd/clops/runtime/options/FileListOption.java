package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.options.FileOption.FileOptionConstraints;

import java.io.File;

public class FileListOption extends ListOption<File> {

  private FileOptionConstraints constraints;
  
  public FileListOption(String identifier, String prefix) {
    super(identifier, prefix);
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
    if (constraints.acceptsProperty(propertyName)) {
      return true;
    } else {
      return super.acceptsProperty(propertyName);
    }
  }

  @Override
  public void setProperty(String propertyName, String propertyValue) throws InvalidOptionPropertyValueException {
    if (!constraints.setProperty(propertyName, propertyValue)) {
      super.setProperty(propertyName, propertyValue);
    }
  }
  
}
