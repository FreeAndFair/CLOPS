package ie.ucd.clops.runtime.parser;

import ie.ucd.clops.runtime.flyrules.FlyRuleStore;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.options.OptionStore;

import java.util.ArrayList;
import java.util.Arrays;

public abstract class AbstractSpecificCLParser {

  public abstract OptionStore createOptions() throws InvalidOptionPropertyValueException;
  
  public abstract String getFormatString();
  
  public abstract FlyRuleStore createFlyRules();
  
  public boolean parse(String[] args) throws Exception {
    System.out.println("Received args: " + new ArrayList<String>(Arrays.asList(args)));
    GenericCLParser parser = new GenericCLParser();
    try {
      return parser.parse(getFormatString(), createOptions(), createFlyRules(), args);
    } catch (InvalidOptionPropertyValueException iopve) {
      System.out.println("Error initialising Option properties. " + iopve);
      return false;
    }
  }
  
}
