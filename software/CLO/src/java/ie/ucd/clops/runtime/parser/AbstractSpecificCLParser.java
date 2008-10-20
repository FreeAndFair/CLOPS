package ie.ucd.clops.runtime.parser;

import ie.ucd.clops.runtime.options.OptionStore;

public abstract class AbstractSpecificCLParser {

  public abstract OptionStore createOptions();
  
  public abstract String getFormatString();
  
  public boolean parse(String[] args) throws Exception {
    GenericCLParser parser = new GenericCLParser();
    return parser.parse(getFormatString(), createOptions(), args);
  }
  
}
