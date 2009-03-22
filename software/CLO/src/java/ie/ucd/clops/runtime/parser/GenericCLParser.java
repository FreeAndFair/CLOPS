package ie.ucd.clops.runtime.parser;

import ie.ucd.clops.logging.CLOLogger;
import ie.ucd.clops.runtime.automaton.Automaton;
import ie.ucd.clops.runtime.automaton.AutomatonException;
import ie.ucd.clops.runtime.automaton.Token;
import ie.ucd.clops.runtime.automaton.Tokenizer;
import ie.ucd.clops.runtime.options.CLOPSErrorOption;
import ie.ucd.clops.runtime.options.IMatchable;
import ie.ucd.clops.runtime.options.InvalidOptionValueException;
import ie.ucd.clops.runtime.options.Option;
import ie.ucd.clops.runtime.options.OptionStore;
import ie.ucd.clops.runtime.rules.RuleStore;

import static ie.ucd.clops.runtime.options.IMatchable.SEP;

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
  static final private class ParseStep {
    public Option<?> option;
    public String optionValue;
    public int optionMatchLength;

    public ParseStep(Option<?> option) {
      this.option = option;
      optionMatchLength = option.getMatchLength();
      optionValue = option.getMatchingValueString();
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

  /** 
   * If there is exactly one way to parse the command line
   * then it parses the command line and returns {@code true},
   * otherwise returns {@code false}. Errors in the DSL may cause
   * this function to throw exception. Exceptions may also be
   * thrown if options refuse to set their values from the given
   * string.
   *
   * TODO(rgrig): The interface of this function should clearly
   *    separate errors in the DSL from errors in the command line.
   */
  public boolean alternateParse(
      String formatString, 
      OptionStore optionStore,
      RuleStore ruleStore,
      String[] args) 
  throws 
      Tokenizer.IllegalCharacterException, 
      Tokenizer.UnknownOptionException ,
      AutomatonException,
      InvalidOptionValueException
  {
    this.optionStore = optionStore;
    this.ruleStore = ruleStore;
    buildAutomaton(formatString);
    buildCommandLine(args);

    parsingPossibilities = new HashSet<ArrayList<ParseStep>>();
    currentParse = new ArrayList<ParseStep>();

    recursiveParse(0);
    if (parsingPossibilities.size() != 1) {
      log.fine("There are " + parsingPossibilities.size() + 
          " parsing possibilities.");
      return false;
    }
    applyParse(parsingPossibilities.iterator().next());
    ruleStore.applyValidityRules(optionStore);
    List<String> validityErrorList = 
        ((CLOPSErrorOption)optionStore.getOptionByIdentifier(
            CLOPSErrorOption.ERROR_OPTION_ID)).getValue();
    for (String error : validityErrorList)
      log.fine(error);
    return validityErrorList.isEmpty();
  }

  private void recursiveParse(int startIndex) {
    if (startIndex == commandLine.length()) {
      if (automaton.isAccepting())
        parsingPossibilities.add(new ArrayList<ParseStep>(currentParse));
      return;
    }

    Collection<IMatchable> possibleTransitions = 
        automaton.availableTransitionsUnique();
    Map<ParseStep, Set<IMatchable>> matches =
        new HashMap<ParseStep, Set<IMatchable>>();
    for (IMatchable t : possibleTransitions) {
      Option<?> option = t.getMatchingOption(commandLine, startIndex);
      if (option == null) continue;
      ParseStep step = new ParseStep(option);
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
    }
  }

  private void applyParse(List<ParseStep> parse) 
  throws InvalidOptionValueException {
    for (ParseStep step : parse) {
      step.option.setFromString(step.optionValue);
      log.fine("Set option: " + step.option);
      ruleStore.applyFlyRules(step.option, optionStore);
    }
    ruleStore.applyOverrideRules(optionStore);
  }

  private void buildAutomaton(String formatString) 
  throws 
      Tokenizer.IllegalCharacterException, 
      Tokenizer.UnknownOptionException,
      AutomatonException
  {
    List<Token<IMatchable>> tokens =
      new Tokenizer().tokenize(formatString, optionStore);
    automaton = new Automaton<IMatchable>(tokens);
  }

  private void buildCommandLine(String[] args) {
    StringBuilder sb = new StringBuilder();
    for (String a : args) {
      sb.append(a);
      sb.append(SEP);
    }
    commandLine = sb.toString();
  }


  /**
   * Parse the given commandline.
   * @param formatString the format regular expression in a string form
   * @param flyStore collection of fly rules that should be used during parsing
   * @param optionStore collection of options that will be matched against the input
   * @param args the commandline as given to the main method
   * @return {@code true} iff the commmandline has been successfully parsed
   */
  public boolean parse(String formatString, OptionStore optionStore, RuleStore flyStore, String[] args)
  throws Tokenizer.IllegalCharacterException,
  Tokenizer.UnknownOptionException {
    CLOLogger.getLogger().log(Level.FINE, "Number of args: " + args.length);
    CLOLogger.getLogger().log(Level.FINE, Arrays.asList(args).toString());

    CLOLogger.getLogger().log(Level.FINE, flyStore.toString());

    //Set up automaton
    List<Token<IMatchable>> tokens = null;
    Automaton<IMatchable> automaton = null;
    try {
      tokens = new Tokenizer().tokenize(formatString, optionStore);
    }
    catch (Tokenizer.UnknownOptionException e) {
      CLOLogger.getLogger().log(Level.SEVERE, "Error: Unkown option name \"" +e.opt_name +"\".");
      throw e;
    }
    catch (Tokenizer.IllegalCharacterException e) {
      //TODO: logger?
      CLOLogger.getLogger().log(Level.SEVERE, "Error: Illegal character \"" +formatString.charAt( e.index)
          +"\" at position " +e.index +".");
      throw e;
    }

    try {
      automaton = new Automaton<IMatchable>(tokens);
    }
    catch (AutomatonException e) {
      // TODO: Exception refinement
      CLOLogger.getLogger().log(Level.SEVERE, "Error: Automaton exception.");
      return false;
    }

    //Convert args to single string
    StringBuilder sb = new StringBuilder();
    for (String arg : args) {
      sb.append(arg);
      sb.append(SEP);
    }
    String argumentString = sb.toString();

    //Main loop
    for (int i=0; i < argumentString.length(); ) {
      //Get available next options
      Collection<IMatchable> possibleTransitions = automaton.availableTransitionsUnique();
      CLOLogger.getLogger().log(Level.FINE, "Transitions: " + possibleTransitions);
      CLOLogger.getLogger().log(Level.FINE, "Set options: ");
      CLOLogger.getLogger().log(Level.FINE, optionStore.toString());

      //Matched option
      Option<?> matchedOption = null;
      Set<IMatchable> matches = new HashSet<IMatchable>();

      //Try and find a match
      for (IMatchable transition : possibleTransitions) {
        Option<?> newMatchedOption = transition.getMatchingOption(argumentString, i);
        if (newMatchedOption != null) {
          //We cannot match on two different Options
          if (matchedOption != null && matchedOption != newMatchedOption) {
            CLOLogger.getLogger().log(Level.SEVERE, "Matched two options: " 
              + matchedOption + " and " + newMatchedOption);
            return false;
          }

          matchedOption = newMatchedOption;
          matches.add(transition);
        }
      }


      if (matchedOption == null) {  
        // If no  match was found
        CLOLogger.getLogger().log(Level.SEVERE, "Illegal option: " + suggestUnmatchedOption(argumentString, i)); // debugging
        return false;
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
          return false;
        } else {
          i += matchedOption.getMatchLength();
          try {
            CLOLogger.getLogger().log(Level.FINE, "Applying fly rules");
            flyStore.applyFlyRules(matchedOption, optionStore);
            CLOLogger.getLogger().log(Level.FINE, "Done applying fly rules");
          } catch (InvalidOptionValueException iove) {
            //Shouldn't happen?
            CLOLogger.getLogger().log(Level.SEVERE, "Invalid option value set from fly rule: " + iove);
            return false;
          }
        }
      }

    }

    CLOLogger.getLogger().log(Level.FINE, "finished parsing");
    CLOLogger.getLogger().log(Level.FINE, "Final Option values: ");
    CLOLogger.getLogger().log(Level.FINE, optionStore.toString());
    CLOLogger.getLogger().log(Level.FINE, "Accepting: " + automaton.isAccepting());

    if (automaton.isAccepting()) {
      try {
        flyStore.applyOverrideRules(optionStore);
        CLOLogger.getLogger().log(Level.FINE, "Override rules complete.");
      } catch (InvalidOptionValueException e) {
        //Again, shouldn't happen?
        CLOLogger.getLogger().log(Level.SEVERE, "Invalid option value set from override rule: " + e);
        return false;
      }


      try {
        flyStore.applyValidityRules(optionStore);
        CLOLogger.getLogger().log(Level.FINE, "Validity checks complete.");
      } catch (InvalidOptionValueException e) {
        //Really, really shouldn't happen
        CLOLogger.getLogger().log(Level.SEVERE, "Something internal went wrong.");
        return false;
      }
      List<String> validityErrorList = ((CLOPSErrorOption)optionStore.getOptionByIdentifier(CLOPSErrorOption.ERROR_OPTION_ID)).getValue();
      if (validityErrorList.size() > 0) {
        //We had a validity error.
        CLOLogger.getLogger().log(Level.SEVERE, "Validity check failed.");
        for (String errorMessage : validityErrorList) {
          if (errorMessage != null && !errorMessage.equals("")) { 
            CLOLogger.getLogger().log(Level.SEVERE, errorMessage);
          }
        }
        return false;
      } else {
        CLOLogger.getLogger().log(Level.FINE, "Validity checks passed.");
      }

      return true;
    } else {
      return false;
    }

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
