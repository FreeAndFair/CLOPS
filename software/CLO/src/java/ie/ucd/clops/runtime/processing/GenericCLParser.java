
package ie.ucd.clops.runtime.processing;

import ie.ucd.clops.runtime.options.*;
import ie.ucd.clops.runtime.parser.ProcessingResult;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

/**
 * Class parsing the command-line, for the moment it's not taking into
 * account the regular expression describing the allowed formats.
 *
 * @author Mikolas Janota
 * @author Fintan
 * @author Viliam Holub
 */
public class GenericCLParser {
    List<String> arguments;
    Set<Option> options;

    /**
     * @param options instances of runtime descriptions of options
     * @param flyRules set of fly rules to be executed on the options
     */
    public GenericCLParser(Set<Option> options) {
        this.options = new HashSet<Option>(options);
    }
    
    public void parse(String formatString, String[] args) throws Exception {
      
      //Set up automaton
      Collection<Token<IMatchable>> tokens = new Tokenizer().tokenize(formatString, null);
      Automaton<IMatchable> automaton = new Automaton<IMatchable>(tokens);
      
      //Main loop
      for (int i=0; i < args.length; ) {
        //Get available next options
        Collection<IMatchable> nextStates = automaton.availableTransitions();
        
        //Matched option
        Option matchedOption = null;
                
        //Try and find a match
        for (Object o : nextStates) {
          IMatchable state = (IMatchable)o;
          matchedOption = state.getMatchingOption(args[i]);
          if (matchedOption != null) {
            automaton.nextStep(state);
            break;
          }
        }
        
        //If we found a match
        if (matchedOption == null) {
          //Check if we can have a program argument here...
          //if not, report error 
        } else {
          ProcessingResult pr = matchedOption.process(args, i);
          if (pr.errorDuringProcessing()) {
            //output error
            System.out.println(pr.getErrorMessage());
          } else {
            i += pr.getNumberOfArgsConsumed();
            //Apply fly rule
          }
        }
        
      }
      
    }
    
}
