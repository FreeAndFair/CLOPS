package ie.ucd.clops.dsl.generatedinterface;

import java.io.PrintStream;
import java.util.List;

import ie.ucd.clops.runtime.errors.ParseResult;
import ie.ucd.clops.runtime.options.Option;
import ie.ucd.clops.runtime.options.exception.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.parser.AbstractSpecificCLParser;
import ie.ucd.clops.runtime.rules.RuleStore;
import ie.ucd.clops.util.OptionUtil;

/**
 * The arguments parser.
 * This is the main entry point for the option's handling.
 * @author The CLOPS team
 */
public class CLODSLParser extends AbstractSpecificCLParser {

  /** The option store used to hold the option's status. */
  private final CLODSLOptionStore optionStore;
  /** The store which contains the constraints associated with the options. */
  private final ie.ucd.clops.runtime.rules.RuleStore ruleStore;

  /**
   * Creates a parser to handle the options.
   * @throws InvalidOptionPropertyValueException if one of the options had
   * an invalid property attached to it in the CLOPS description file.
   */
  public CLODSLParser() throws InvalidOptionPropertyValueException {
    optionStore = new CLODSLOptionStore();
    ruleStore = new CLODSLRuleStore();
  }

  /**
   * Get the {@link ie.ucd.clops.runtime.options.OptionStore} containing the option instances for this parser.
   * @return the option store.
   */
  public CLODSLOptionStore getOptionStore() {
    return optionStore;  
  }
  
  /**
   * Get the {@link RuleStore} containing the rules for this parser.
   * @return the option store.
   */
  public RuleStore getRuleStore() {
    return ruleStore;
  }
  
  /**
   * Get the format string for this parser.
   * @return the format string.
   */
  public String getFormatString() {
    return "(All* Input All*) | Version"; 
  }

  public static void printUsage(PrintStream os) {
    printUsage(os, 80, 0);
  }

  public static void printUsage(PrintStream out, int width, int indent) {
    List<Option<?>> all = new CLODSLOptionStore().getOptionsWithoutErrorOption();
    OptionUtil.printOptions(out, all, width, indent);
    out.flush();
  }
  
  /**
   * Parse the given command line arguments using a new CLODSLParser,
   * with normal lookahead. 
   */
  public static CLODSLParseResult parse(String[] args, String progName) {
    CLODSLParser parser = new CLODSLParser();
    ParseResult parseResult = parser.parseInternal(args, progName);
    return new CLODSLParseResult(parseResult, parser.getOptionStore());
  }
  
  /**
   * Parse the given command line arguments using the provided CLODSLParser,
   * with normal lookahead. 
   */
  public static CLODSLParseResult parse(String[] args, String progName, CLODSLParser parser) {
    ParseResult parseResult = parser.parseInternal(args, progName);
    return new CLODSLParseResult(parseResult, parser.getOptionStore());
  }
  
  /**
   * Parse the given command line arguments using a new CLODSLParser,
   * with infinite lookahead.
   */
  public static CLODSLParseResult parseAlternate(String[] args, String progName) {
    CLODSLParser parser = new CLODSLParser();
    ParseResult parseResult = parser.parseAlternateInternal(args, progName);
    return new CLODSLParseResult(parseResult, parser.getOptionStore());
  }
  
  /**
   * Parse the given command line arguments using the provided CLODSLParser,
   * with infinite lookahead. 
   */
  public static CLODSLParseResult parseAlternate(String[] args, String progName, CLODSLParser parser) {
    ParseResult parseResult = parser.parseAlternateInternal(args, progName);
    return new CLODSLParseResult(parseResult, parser.getOptionStore());
  }
}
