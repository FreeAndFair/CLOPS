
package ie.ucd.clops.runtime.processing;

import ie.ucd.clops.runtime.options.*;
import ie.ucd.clops.runtime.parser.MatchResult;

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
    public GenericCLParser(Set<Option> options, FlyRules flyRules) {
        this.options = new HashSet<Option>(options);
    }



    /**
     * Finds the option that triggers on a given command line string.
     *
     * @param arg a <code>String</code> that came on the command line
     * @param options the set of candidates for matching
     * @return an <code>Option</code> value, returns {@code null} if no such option was found
     */
    Option findMatchingOption(/*@non_null*/String arg, Collection<Option> options) {
        Option matchingOption = null;
        for (Option o : options) {
            //MatchResult mr 
            if (o.doIMatch(arg) ){
                assert matchingOption == null; // find maximally one option that matches on arg
                matchingOption = o;
            }
        }

	return matchingOption;
    }

    /**
     * Fills in the values of {@code options} according to the given command line.
     *
     * @param args a <code>String[]</code> value
     */
    public void parse(/*@non_null*/String[] args) throws Exception {
        int index = 0;
        // init automaton
        while (index < args.length) {
            /* The following automaton code accounts for the case when
             * multiple options (including the argument) could match
             * but only some of them are correct (in some sense). For
             * instance, in "svn add add" the command "add" would
             * match on the argument but this would bring the
             * automaton into the error state as only one command is
             * allowed. This could be solved more generally using
             * backtracking but we believe that such is not needed. 
             * Miko, Viliam */

            // options = automaton.getOptionsThatDoNotLeadToAnErrorState
            // if (options.isEmpty && !automaton.canMatchArgument) ERROR
            Option matchingOption = findMatchingOption(args[index], options);

            if (matchingOption == null) {
                // no option has matched on args[index], store it in arguments
                arguments.add(args[index]);
                ++index;
                // automaton.transition(ARGUMENT)
            } else {
                // process the arguments
                MatchResult mr = matchingOption.match(args, index);
                if (mr.errorDuringProcessing()) {
                    //TODO: actually throw Exception
                    //throw /*up*/ mr.getErrorMessage();
                }
                // TODO: trigger fly rule (could be maybe in a separate stage)
                index += mr.getNumberOfArgsConsumed(); // move forward on the command-line
                // automaton.transition(matchingOption)
            }
            // assert that automaton is in a valid state
        }
        // assert that the automaton is in the final state
    }
}
