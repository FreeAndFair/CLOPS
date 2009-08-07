package ie.ucd.clops.runtime.parser;

import ie.ucd.clops.runtime.errors.ParseResult;
import ie.ucd.clops.runtime.options.OptionStore;
import ie.ucd.clops.runtime.rules.RuleStore;

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
   * Get the {@link OptionStore} containing the option instances
   * for this parser.
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
  public ParseResult parseInternal(String[] args)
  { return parseInternal(args, false); }

  /**
   * Parse the given command line arguments using this parser with the infiniteLookahead. 
   * @param args the command line arguments to parse.
   * @return whether the parse was successful or not
   */
  public ParseResult parseAlternateInternal(String[] args) 
  { return parseInternal(args, true); }

  /**
   * Parse the given command line arguments using this parser. 
   * @param args the command line arguments to parse.
   * @return whether the parse was successful or not
   */
  public ParseResult parseInternal(String[] args, boolean infiniteLookahead) {
    return parse(new GenericCLParser(), args, infiniteLookahead);
  }
  
  /**
   * Parse the given command line arguments using the provided parser.
   * @param parser the parser to use.
   * @param args the command line arguments to parse.
   * @return whether the parse was successful or not.
   */
  public ParseResult parse(GenericCLParser parser, String[] args, boolean infiniteLookahead) {
    if (infiniteLookahead) 
      return parser.alternateParse(getFormatString(), getOptionStore(), getRuleStore(), args);
    else 
      return parser.parse(getFormatString(), getOptionStore(), getRuleStore(), args);
  }
}
