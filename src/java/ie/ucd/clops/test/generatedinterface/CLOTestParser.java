package ie.ucd.clops.test.generatedinterface;

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
public class CLOTestParser extends AbstractSpecificCLParser {

  /** The option store used to hold the option's status. */
  private final CLOTestOptionStore optionStore;
  /** The store which contains the constraints associated with the options. */
  private final ie.ucd.clops.runtime.rules.RuleStore ruleStore;

  /**
   * Creates a parser to handle the options.
   * @throws InvalidOptionPropertyValueException if one of the options had
   * an invalid property attached to it in the CLOPS description file.
   */
  public CLOTestParser() throws InvalidOptionPropertyValueException {
    optionStore = new CLOTestOptionStore();
    ruleStore = new CLOTestRuleStore();
  }

  /**
   * Get the {@link ie.ucd.clops.runtime.options.OptionStore} containing the option instances for this parser.
   * @return the option store.
   */
  public CLOTestOptionStore getOptionStore() {
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
    return "(AllOptions* Input AllOptions*)"; 
  }

  public static void printUsage(PrintStream os) {
    printUsage(os, 80, 0);
  }

  public static void printUsage(PrintStream out, int width, int indent) {
    List<Option<?>> all = new CLOTestOptionStore().getOptionsWithoutErrorOption();
    OptionUtil.printOptions(out, all, width, indent);
    out.flush();
  }
  
  /**
   * Parse the given command line arguments using a new CLOTestParser,
   * with normal lookahead. 
   */
  public static CLOTestParseResult parse(String[] args, String progName) {
    CLOTestParser parser = new CLOTestParser();
    ParseResult parseResult = parser.parseInternal(args, progName);
    return new CLOTestParseResult(parseResult, parser.getOptionStore());
  }
  
  /**
   * Parse the given command line arguments using the provided CLOTestParser,
   * with normal lookahead. 
   */
  public static CLOTestParseResult parse(String[] args, String progName, CLOTestParser parser) {
    ParseResult parseResult = parser.parseInternal(args, progName);
    return new CLOTestParseResult(parseResult, parser.getOptionStore());
  }
  
  /**
   * Parse the given command line arguments using a new CLOTestParser,
   * with infinite lookahead.
   */
  public static CLOTestParseResult parseAlternate(String[] args, String progName) {
    CLOTestParser parser = new CLOTestParser();
    ParseResult parseResult = parser.parseAlternateInternal(args, progName);
    return new CLOTestParseResult(parseResult, parser.getOptionStore());
  }
  
  /**
   * Parse the given command line arguments using the provided CLOTestParser,
   * with infinite lookahead. 
   */
  public static CLOTestParseResult parseAlternate(String[] args, String progName, CLOTestParser parser) {
    ParseResult parseResult = parser.parseAlternateInternal(args, progName);
    return new CLOTestParseResult(parseResult, parser.getOptionStore());
  }
}
