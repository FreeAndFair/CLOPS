package ie.ucd.clops.runtime.parser;

import ie.ucd.clops.logging.CLOLogger;
import ie.ucd.clops.runtime.automaton.Automaton;
import ie.ucd.clops.runtime.automaton.AutomatonException;
import ie.ucd.clops.runtime.automaton.Token;
import ie.ucd.clops.runtime.automaton.Tokenizer;
import ie.ucd.clops.runtime.flyrules.FlyRuleStore;
import ie.ucd.clops.runtime.options.IMatchable;
import ie.ucd.clops.runtime.options.InvalidOptionValueException;
import ie.ucd.clops.runtime.options.Option;
import ie.ucd.clops.runtime.options.OptionStore;

import static ie.ucd.clops.runtime.options.IMatchable.SEP;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;
import java.util.logging.Level;

/**
 * Class parsing the command-line.
 *
 * @author Mikolas Janota
 * @author Fintan
 * @author Viliam Holub
 */
public class GenericCLParser {

  public GenericCLParser() {}

  /**
   * Parse the given commandline.
   * @param formatString the format regular expression in a string form
   * @param flyStore collection of fly rules that should be used during parsing
   * @param optionStore collection of options that will be matched against the input
   * @param args the commandline as given to the main method
   * @return {@code true} iff the commmandline has been successfully parsed
   */
  public boolean parse(String formatString, OptionStore optionStore, FlyRuleStore flyStore, String[] args)
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
          assert matchedOption == null || matchedOption == newMatchedOption;

          matchedOption = newMatchedOption;
          matches.add(transition);
        }
      }

      //If we found a match
      if (matchedOption == null) {
        //Check if we can have a program argument here...
        //if not, report error 
        CLOLogger.getLogger().log(Level.SEVERE, "Illegal option: " + matchedOption); // debugging
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
    return automaton.isAccepting();

  }

}
