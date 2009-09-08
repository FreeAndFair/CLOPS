package ie.ucd.clops.runtime.parser;

import static ie.ucd.clops.runtime.options.IMatchable.SEP_STRING;
import ie.ucd.clops.logging.CLOLogger;
import ie.ucd.clops.runtime.automaton.Automaton;
import ie.ucd.clops.runtime.automaton.Token;
import ie.ucd.clops.runtime.automaton.Tokenizer;
import ie.ucd.clops.runtime.automaton.exception.AutomatonException;
import ie.ucd.clops.runtime.errors.AmbiguousCommandLineError;
import ie.ucd.clops.runtime.errors.IncompleteCommandLineError;
import ie.ucd.clops.runtime.errors.InvalidOptionValueError;
import ie.ucd.clops.runtime.errors.ParseResult;
import ie.ucd.clops.runtime.errors.UnknownOptionError;
import ie.ucd.clops.runtime.errors.ValidityError;
import ie.ucd.clops.runtime.options.CLOPSErrorOption;
import ie.ucd.clops.runtime.options.IMatchable;
import ie.ucd.clops.runtime.options.Option;
import ie.ucd.clops.runtime.options.OptionStore;
import ie.ucd.clops.runtime.options.exception.InvalidOptionValueException;
import ie.ucd.clops.runtime.rules.RuleStore;
import ie.ucd.clops.util.StringUtil;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.logging.Level;
import java.util.logging.Logger;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * Command line parser.
 *
 * @author Mikolas Janota
 * @author Fintan
 * @author Viliam Holub
 */
public class GenericCLParser {

  public static final boolean DO_ERROR_RECOVERY = false;

  private static final Logger log = Logger.getLogger("ie.ucd.clops");

  public GenericCLParser() {}

  /** 
   * Represents a possible way to parse a piece of the command
   * line. The {@code option} matches on the command line string
   * starting at {@code startIndex}. A `parse' is a sequence of
   * parse steps. `Applying a parse step' {@code s} means that we
   * call {@code s.option.setValueFromString(s.optionValue)} (and
   * the corresponding fly rules are applied).
   */
  static final public class ParseStep {
    public Option<?> option;
    public String optionValue;
    public int optionMatchLength;
    public int position;

    public ParseStep(Option<?> option, int position) {
      this.option = option;
      optionMatchLength = option.getMatchLength();
      optionValue = option.getMatchingValueString();
      this.position = position;
    }

    @Override public boolean equals(Object o) {
      if (!(o instanceof ParseStep)) return false;
      ParseStep t = (ParseStep)o;
      if (optionMatchLength != t.optionMatchLength) return false;
      if (option == null ^ t.option == null) return false;
      if (optionValue == null ^ t.optionValue == null) return false;
      return option.equals(t.option) && optionValue.equals(t.optionValue);
    }

    @Override public int hashCode() {
      return 
      optionMatchLength + 
      (option == null? 0 : option.hashCode()) + 
      (optionValue == null? 0 : optionValue.hashCode());
    }
  }

  private HashSet<ArrayList<ParseStep>> parsingPossibilities;
  private ArrayList<ParseStep> currentParse;
  private OptionStore optionStore;
  private RuleStore ruleStore;
  private Automaton<IMatchable> automaton;
  private String commandLine;
  private boolean lookahead;
  private int longestStuckLength;
  private HashSet<ArrayList<ParseStep>> longestStuck;

  /** 
   * If there is exactly one way to parse the command line
   * then it parses the command line and returns {@code true},
   * otherwise returns {@code false}. Errors in the DSL may cause
   * this function to throw exception. Exceptions may also be
   * thrown if options refuse to set their values from the given
   * string.
   */
  public ParseResult alternateParse(
      String formatString, 
      OptionStore optionStore,
      RuleStore ruleStore,
      String[] args)
  throws 
      Tokenizer.IllegalCharacterException, 
      Tokenizer.UnknownOptionException
  {
    ParseResult result = new ParseResult(StringUtil.appendWithSeparator(args, " ", false));

    this.optionStore = optionStore;
    this.ruleStore = ruleStore;
    automaton = buildAutomaton(formatString, optionStore);
    commandLine = StringUtil.appendWithSeparator(args, SEP_STRING, true);

    parsingPossibilities = new HashSet<ArrayList<ParseStep>>();
    currentParse = new ArrayList<ParseStep>();
    longestStuckLength = -1;

    recursiveParse(0);
    describeErrors(result);
    if (!result.successfulParse()) {
      return result;
    }
    result.addAll(applyParse(parsingPossibilities.iterator().next()));
    if (!result.successfulParse()) {
      return result;
    }

    ruleStore.applyValidityRules(optionStore);
    List<String> validityErrorList = 
      ((CLOPSErrorOption)optionStore.getOptionByIdentifier(
          CLOPSErrorOption.ERROR_OPTION_ID)).getRawValue();
    for (String error : validityErrorList) {
      log.fine(error);
      result.addError(new AmbiguousCommandLineError(error));
    }
    return result;
  }

  private void describeErrors(ParseResult result) {
    if (parsingPossibilities.size() > 1) {
      log.fine("There are " + parsingPossibilities.size() + " parsing possibilities.");
      //TODO better errors here - index of divergence, other information
      result.addError(new AmbiguousCommandLineError("There are " + parsingPossibilities.size() + " parsing possibilities."));
    } else if (parsingPossibilities.size() == 0) {
      log.fine("There are " + parsingPossibilities.size() + " parsing possibilities.");
      result.addError(new UnknownOptionError(longestStuckLength, longestStuck));
    }
  }

  private void recordStuck(int startIndex) {
    if (startIndex < longestStuckLength) {
      return;
    }
    if (startIndex > longestStuckLength) {
      longestStuck = new HashSet<ArrayList<ParseStep>>();
      longestStuckLength = startIndex;
    }
    longestStuck.add(new ArrayList<ParseStep>(currentParse));
  }

  private void recursiveParse(int startIndex) {
    if (startIndex == commandLine.length()) {
      if (automaton.isAccepting()) {
        parsingPossibilities.add(new ArrayList<ParseStep>(currentParse));
      } else {
        recordStuck(startIndex);
      }
      return;
    }

    Collection<IMatchable> possibleTransitions = 
      automaton.availableTransitionsUnique();
    Map<ParseStep, Set<IMatchable>> matches =
      new HashMap<ParseStep, Set<IMatchable>>();
    for (IMatchable t : possibleTransitions) {
      Option<?> option = t.getMatchingOption(commandLine, startIndex);
      if (option == null) continue;
      ParseStep step = new ParseStep(option, startIndex);
      Set<IMatchable> transitions = matches.get(step);
      if (transitions == null) {
        transitions = new HashSet<IMatchable>();
        matches.put(step, transitions);
      }
      transitions.add(t);
    }
    for (Map.Entry<ParseStep, Set<IMatchable>> e : matches.entrySet()) {
      automaton.nextStep(e.getValue());
      currentParse.add(e.getKey());
      recursiveParse(startIndex + e.getKey().optionMatchLength);
      currentParse.remove(currentParse.size() - 1);
      automaton.previousStep();
      if (!lookahead) break;
    }
    if (matches.isEmpty()) {
      recordStuck(startIndex);
    }
  }

  private ParseResult applyParse(List<ParseStep> parse) {
    ParseResult result = new ParseResult();
    for (ParseStep step : parse) {
      try {
        step.option.setFromString(step.optionValue);
      } catch (InvalidOptionValueException e) {
        result.addError(new InvalidOptionValueError(e.getMessage(), step.position));
      }

      if (result.successfulParse()) {
        log.fine("Set option: " + step.option);
        result.addAll(ruleStore.applyFlyRules(step.option, optionStore));
      }

      if (!DO_ERROR_RECOVERY && !result.successfulParse()) {
        return result;
      }
    }
    result.addAll(ruleStore.applyOverrideRules(optionStore));
    return result;
  }

  private static Automaton<IMatchable> buildAutomaton(String formatString, OptionStore optionStore) 
  throws 
  Tokenizer.IllegalCharacterException, 
  Tokenizer.UnknownOptionException,
  AutomatonException
  {
    List<Token<IMatchable>> tokens =
      new Tokenizer().tokenize(formatString, optionStore);
    return new Automaton<IMatchable>(tokens);
  }


  private static void logParseStart(String[] args, RuleStore ruleStore) {
    CLOLogger.getLogger().log(Level.FINE, "Number of args: " + args.length);
    CLOLogger.getLogger().log(Level.FINE, Arrays.asList(args).toString());
    CLOLogger.getLogger().log(Level.FINE, ruleStore.toString());
  }

  private static void logPossibleTransitions(Collection<IMatchable> transitions, OptionStore optionStore) {
    CLOLogger.getLogger().log(Level.FINE, "Transitions: " + transitions);
    CLOLogger.getLogger().log(Level.FINE, "Set options: ");
    CLOLogger.getLogger().log(Level.FINE, optionStore.toString());
  }

  private static void logFinishedParsing(OptionStore optionStore, Automaton<IMatchable> automaton) {
    CLOLogger.getLogger().log(Level.FINE, "finished parsing");
    CLOLogger.getLogger().log(Level.FINE, "Final Option values: ");
    CLOLogger.getLogger().log(Level.FINE, optionStore.toString());
    CLOLogger.getLogger().log(Level.FINE, "Accepting: " + automaton.isAccepting());
  }

  private static ParseResult applyOverridesAndCheckValidity(ParseResult result, OptionStore optionStore, Automaton<IMatchable> automaton, RuleStore ruleStore) {
    if (automaton.isAccepting()) {

      result.addAll(ruleStore.applyOverrideRules(optionStore));
      CLOLogger.getLogger().log(Level.FINE, "Override rules complete.");

      if (!result.successfulParse()) {
        return result;
      }

      ruleStore.applyValidityRules(optionStore);
      CLOLogger.getLogger().log(Level.FINE, "Validity checks complete.");

      List<String> validityErrorList = ((CLOPSErrorOption)optionStore.getOptionByIdentifier(CLOPSErrorOption.ERROR_OPTION_ID)).getRawValue();
      if (!validityErrorList.isEmpty()) {
        CLOLogger.getLogger().log(Level.FINE, "Validity check failed.");
        for (String errorMessage : validityErrorList) {
          if (errorMessage != null && !errorMessage.equals("")) { 
            CLOLogger.getLogger().log(Level.FINE, errorMessage);
            result.addError(new ValidityError(errorMessage));
          }
        }
        return result;
      } else {
        CLOLogger.getLogger().log(Level.FINE, "Validity checks passed.");
      }

      return result;
    } else {
      CLOLogger.getLogger().log(Level.SEVERE, "Invalid arguments.");
      //TODO print usage string? print possible next args?
      result.addError(new IncompleteCommandLineError("Invalid arguments."));
      return result;
    }
  }
  
  private static ParseResult mainParseLoop(String[] args, OptionStore optionStore, RuleStore ruleStore, Automaton<IMatchable> automaton) {
    //Convert args to single string
    String argumentString = StringUtil.appendWithSeparator(args, SEP_STRING, true);
    ParseResult result = new ParseResult(StringUtil.appendWithSeparator(args, " ", false));
    //Main loop
    for (int i=0; i < argumentString.length(); ) {
      //Get available next options
      Collection<IMatchable> possibleTransitions = automaton.availableTransitionsUnique();
      logPossibleTransitions(possibleTransitions, optionStore);

      //Matched option
      Option<?> matchedOption = null;
      Set<IMatchable> matches = new HashSet<IMatchable>();

      //Try and find a match
      for (IMatchable transition : possibleTransitions) {
        Option<?> newMatchedOption = transition.getMatchingOption(argumentString, i);
        if (newMatchedOption != null) {
          //We cannot match on two different Options
          if (matchedOption != null && matchedOption != newMatchedOption) {
            CLOLogger.getLogger().log(Level.SEVERE, "Matched two options: " + matchedOption + " and " + newMatchedOption);
            result.addError(new AmbiguousCommandLineError("Matched two options: " + matchedOption + " and " + newMatchedOption));
            return result;
          }

          matchedOption = newMatchedOption;
          matches.add(transition);
        }
      }


      if (matchedOption == null) {  
        // If no  match was found
        CLOLogger.getLogger().log(Level.SEVERE, "Illegal option: " + suggestUnmatchedOption(argumentString, i)); // debugging
        //TODO index of no match
        result.addError(new UnknownOptionError(i, suggestUnmatchedOption(argumentString, i)));
        return result;
      } else {
        //We should have at least one transition
        assert matches.size() > 0;
        //Update automaton
        CLOLogger.getLogger().log(Level.FINE, "Matches: " + matches);
        automaton.nextStep(matches);

        CLOLogger.getLogger().log(Level.FINE, "Matched option: " + matchedOption);

        ProcessingResult pr = matchedOption.process();
        if (pr.errorDuringProcessing()) {
          //output error
          CLOLogger.getLogger().log(Level.SEVERE, pr.getErrorMessage());
          result.addError(new InvalidOptionValueError(pr.getErrorMessage(), i));
          if (!DO_ERROR_RECOVERY) {
            return result;
          }
        } else {
          i += matchedOption.getMatchLength();
          CLOLogger.getLogger().log(Level.FINE, "Applying fly rules");
          result.addAll(ruleStore.applyFlyRules(matchedOption, optionStore));
          CLOLogger.getLogger().log(Level.FINE, "Done applying fly rules");
          if (!DO_ERROR_RECOVERY && !result.successfulParse()) {
            return result;
          }
        }
      }

    }
    return result;
  }

  /**
   * Parse the given commandline.
   * @param formatString the format regular expression in a string form
   * @param ruleStore collection of fly rules that should be used during parsing
   * @param optionStore collection of options that will be matched against the input
   * @param args the commandline as given to the main method
   * @return {@code true} iff the commmand line has been successfully parsed.
   */
  public ParseResult parse(String formatString, OptionStore optionStore, RuleStore ruleStore, String[] args) {
    logParseStart(args, ruleStore);

    Automaton<IMatchable> automaton = buildAutomaton(formatString, optionStore);
    ParseResult result = mainParseLoop(args, optionStore, ruleStore, automaton);

    logFinishedParsing(optionStore, automaton);

    return applyOverridesAndCheckValidity(result, optionStore, automaton, ruleStore);
  }

  private static final Pattern unmatcher = Pattern.compile(Option.SEP + "*[^" + Option.SEP_STRING + "]+");
  private static String suggestUnmatchedOption(String argumentString, int offset) {
    Matcher matcher = unmatcher.matcher(argumentString);
    matcher.region(offset, argumentString.length());

    if (matcher.lookingAt()) {
      return matcher.group();
    } else {
      return "";
    }
  }

}
