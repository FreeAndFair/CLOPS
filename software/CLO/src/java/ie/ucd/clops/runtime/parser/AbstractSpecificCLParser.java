package ie.ucd.clops.runtime.parser;

import java.util.ArrayList;
import java.util.Arrays;

import ie.ucd.clops.runtime.options.OptionStore;

public abstract class AbstractSpecificCLParser {

  public abstract OptionStore createOptions();
  
  public abstract String getFormatString();
  
  public boolean parse(String[] args) throws Exception {
    System.out.println("Received args: " + new ArrayList<String>(Arrays.asList(args)));
    GenericCLParser parser = new GenericCLParser();
    return parser.parse(getFormatString(), createOptions(), args);
  }
  
}
