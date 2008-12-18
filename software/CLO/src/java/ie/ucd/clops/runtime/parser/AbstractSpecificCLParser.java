package ie.ucd.clops.runtime.parser;

import ie.ucd.clops.logging.CLOLogger;
import ie.ucd.clops.runtime.automaton.Tokenizer.IllegalCharacterException;
import ie.ucd.clops.runtime.automaton.Tokenizer.UnknownOptionException;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.options.OptionStore;
import ie.ucd.clops.runtime.rules.RuleStore;

import java.util.logging.Level;

/**
 * This class is used as a base class for the automatically generated parser.
 */
public abstract class AbstractSpecificCLParser {
  
  public AbstractSpecificCLParser() throws InvalidOptionPropertyValueException {
    
  }
  
  public abstract String getFormatString();
  
  public abstract OptionStore getOptionStore();

  public abstract RuleStore getRuleStore();

  public boolean parse(String[] args) {
    return parse(new GenericCLParser(), args);
  }
  
  public boolean parse(GenericCLParser parser, String[] args) {
    try {
      return parser.parse(getFormatString(), getOptionStore(), getRuleStore(), args);
    } catch (IllegalCharacterException e) {
      CLOLogger.getLogger().log(Level.SEVERE, "Error initialising automaton. " + e);
      return false;
    } catch (UnknownOptionException e) { 
      CLOLogger.getLogger().log(Level.SEVERE, "Error initialising automaton. " + e);
      return false;
    }
  }
  
}
