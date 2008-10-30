package ie.ucd.clops.runtime.parser;

import ie.ucd.clops.runtime.automaton.Automaton;
import ie.ucd.clops.runtime.automaton.AutomatonException;
import ie.ucd.clops.runtime.automaton.Token;
import ie.ucd.clops.runtime.automaton.Tokenizer;
import ie.ucd.clops.runtime.flyrules.FlyRuleStore;
import ie.ucd.clops.runtime.options.IMatchable;
import ie.ucd.clops.runtime.options.InvalidOptionValueException;
import ie.ucd.clops.runtime.options.Option;
import ie.ucd.clops.runtime.options.OptionAssignment;
import ie.ucd.clops.runtime.options.OptionStore;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Class parsing the command-line.
 *
 * @author Mikolas Janota
 * @author Fintan
 * @author Viliam Holub
 */
public class GenericCLParser {

  public GenericCLParser() {}

  public boolean parse(String formatString, OptionStore optionStore, FlyRuleStore flyStore, String[] args)
      throws Tokenizer.IllegalCharacterException,
             Tokenizer.UnknownOptionException {

    System.out.println(flyStore.toString());
    
    //Set up automaton
    List<Token<IMatchable>> tokens = null;
    Automaton<IMatchable> automaton = null;
    try {
      tokens = new Tokenizer().tokenize(formatString, optionStore);
    }
    catch (Tokenizer.UnknownOptionException e) {
        //TODO: logger?
        System.err.println( "Error: Unkown option name \"" +e.opt_name +"\".");
        throw e;
    }
    catch (Tokenizer.IllegalCharacterException e) {
        //TODO: logger?
        System.err.println( "Error: Illegal character \"" +formatString.charAt( e.index)
                            +"\" at position " +e.index +".");
        throw e;
    }

    try {
      automaton = new Automaton<IMatchable>(tokens);
    }
    catch (AutomatonException e) {
      // TODO: Exception refinement
      System.err.println( "Error: Automaton exception.");
      System.exit( 1);
    }

    //Main loop
    for (int i=0; i < args.length; ) {
      //Get available next options
      Collection<IMatchable> possibleTransitions = automaton.availableTransitionsUnique();
      System.out.println("Transitions: " + possibleTransitions);
      System.out.print("Set options: ");
      optionStore.printSetOptions(System.out);
      System.out.println();
      
      //Matched option
      Option matchedOption = null;
      Set<IMatchable> matches = new HashSet<IMatchable>();
      
      //Try and find a match
      for (IMatchable transition : possibleTransitions) {
        Option newMatchedOption = transition.getMatchingOption(args[i]);
        if (newMatchedOption != null) {
          //We cannot match on two different Options
          assert matchedOption == null || matchedOption == newMatchedOption;
          //System.out.println("Matched: " + newMatchedOption);
          matchedOption = newMatchedOption;
          matches.add(transition);
          //automaton.nextStep(transition);
          break;
        }
      }

      //If we found a match
      if (matchedOption == null) {
        //Check if we can have a program argument here...
        //if not, report error 
        System.out.println("illegal option: " + args[i]); // debugging
        i++;
        return false;
      } else {
        //We should have at least one transition
        assert matches.size() > 0;
        //Update automaton
        automaton.nextStep(matches);
        
        System.out.println("Matched option: " + matchedOption);
        
        ProcessingResult pr = matchedOption.process(args, i);
        if (pr.errorDuringProcessing()) {
          //output error
          System.out.println(pr.getErrorMessage());
        } else {
          i += pr.getNumberOfArgsConsumed();
          //Apply override rule
          Collection<OptionAssignment> assignments = flyStore.getAssignmentsForOption(matchedOption);
          if (assignments != null) {
            System.out.println("Assignments for " + matchedOption);
            for (OptionAssignment assignment : assignments) {
              Option optionToSet = optionStore.getOptionByIdentifier(assignment.getOptionIdentifier());
              try {
                optionToSet.setFromString(assignment.getOptionValue());
              } catch (InvalidOptionValueException iove) {
                System.out.println(iove);
              }
            }          
          }
        }
      }

    }

    System.out.println("finished parsing"); // debugging
    System.out.println("Final Option values: ");
    optionStore.printSetOptions(System.out);
    return true;

  }

}
