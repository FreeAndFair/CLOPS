package ie.ucd.clops.runtime.parser;

import ie.ucd.clops.logging.CLOLogger;
import ie.ucd.clops.runtime.automaton.AutomatonException;
import ie.ucd.clops.runtime.automaton.Tokenizer.IllegalCharacterException;
import ie.ucd.clops.runtime.automaton.Tokenizer.UnknownOptionException;
import ie.ucd.clops.runtime.options.InvalidOptionValueException;
import ie.ucd.clops.runtime.options.OptionStore;
import ie.ucd.clops.runtime.rules.RuleStore;

import java.util.logging.Level;

/**
 * This class is used as a base class for the automatically generated parser.
 */
public abstract class AbstractSpecificCLParser {

  /**
   * Get the format string for this parser.
   * @return the format string.
   */
  public abstract String getFormatString();
  
  /**
   * Get the {@link OptionStore} containing the option instances for this parser.
   * @return the option store.
   */
  public abstract OptionStore getOptionStore();

  /**
   * Get the {@link RuleStore} containing the rules for this parser.
   * @return the option store.
   */
  public abstract RuleStore getRuleStore();

  /**
   * Parse the given command line arguments using this parser. 
   * @param args the command line arguments to parse.
   * @return whether the parse was successful or not
   */
  public boolean parse(String[] args) 
  throws AutomatonException, InvalidOptionValueException {
    return parse(new GenericCLParser(), args);
  }
  
  /**
   * Parse the given command line arguments using the provided parser.
   * @param parser the parser to use.
   * @param args the command line arguments to parse.
   * @return whether the parse was successful or not.
   */
  // TODO(rgrig): I think this should throw exceptions rather than log them.
  public boolean parse(GenericCLParser parser, String[] args) 
  throws AutomatonException, InvalidOptionValueException {
    try {
      return parser.parse(getFormatString(), getOptionStore(), getRuleStore(), args);
      //return parser.alternateParse(getFormatString(), getOptionStore(), getRuleStore(), args);
    } catch (IllegalCharacterException e) {
      CLOLogger.getLogger().log(Level.SEVERE, "Error initialising automaton. " + e);
      return false;
    } catch (UnknownOptionException e) { 
      CLOLogger.getLogger().log(Level.SEVERE, "Error initialising automaton. " + e);
      return false;
    }
  }
  
}
