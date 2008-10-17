package ie.ucd.clops.runtime.processing;

import ie.ucd.clops.runtime.options.*;
import ie.ucd.clops.runtime.parser.ProcessingResult;

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
    List<String> arguments;
    Set<Option> options;

    /**
     * @param options instances of runtime descriptions of options
     */
    public GenericCLParser(Set<Option> options) {
        this.options = new HashSet<Option>(options);
    }
    
   public boolean parse(String formatString, OptionStore optionStore, String[] args) throws Exception {
      
      //Set up automaton
      Collection<Token<IMatchable>> tokens = new Tokenizer().tokenize(formatString, optionStore);
      Automaton<IMatchable> automaton = new Automaton<IMatchable>(tokens);
      
      //Main loop
      for (int i=0; i < args.length; ) {
        //Get available next options
        Collection<IMatchable> possibleTransitions = automaton.availableTransitions();
        
        //Matched option
        Option matchedOption = null;
                
        //Try and find a match
        for (IMatchable transition : possibleTransitions) {
          matchedOption = transition.getMatchingOption(args[i]);
          if (matchedOption != null) {
            automaton.nextStep(transition);
            break;
          }
        }
        
        //If we found a match
        if (matchedOption == null) {
          //Check if we can have a program argument here...
          //if not, report error 
           System.out.println("illegal option"); // debugging
           i++;
           return false;
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

      System.out.println("finished parsing"); // debugging
      return true;
     
    }

   /*==== Testing ====*/
   private static Set<String> singleton(String s) {
      Set<String> retv = new HashSet<String>(1);
      retv.add(s);
      return retv;
   }

   public static void main(String[] args) throws Exception {
      OptionStore os = new OptionStore();
      BooleanOption bo1 = new BooleanOption("bo1", singleton("-bo"));
      BooleanOption bo2 = new BooleanOption("bo2", singleton("-boo"));

      os.addOption(bo1);
      os.addOption(bo2);

      GenericCLParser gp = new GenericCLParser(os.getOptions());
      assert !gp.parse("-bo", os, new String[] {"-boo"}); // shouldn't parse
      assert gp.parse("-boo", os, new String[] {"-boo"}); // should parse
      assert gp.parse("-boo?", os, new String[] {"-boo"}); // should parse
      assert gp.parse("-boo*", os, new String[] {"-boo" , "-boo" , "-boo"}); // should parse

      assert gp.parse("-boo* -bo*", os, new String[] {"-boo" , "-boo" , "-boo", "-bo", "-bo"}); // should parse

      assert !gp.parse("-boo+ -bo*", os, new String[] {"-bo"}); // shouldn't go thru

      assert gp.parse("(-boo | -bo)*", os, new String[] {"-bo", "-boo", "-bo", "-bo", "-boo"}); // should parse

      assert gp.parse("-boo*", os, new String[] {"-boo", "-boo", "-boo"}); // should parse

      assert !gp.parse("-bo", os, new String[] {"xxxx"});

      try {
          gp.parse("xxx", os, new String[] {"-boo"});
          assert false;
      } catch (Tokenizer.UnknownOptionException e) {
          assert true;
      }
   }
    
}
