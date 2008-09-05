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
     * @param arg a a <code>String</code> that came on the command line
     * @return an <code>Option</code> value, returns {@code null} if no such option was found
     */
    Option findMatchingOption(/*@non_null*/String arg) {
        for (Option o : options) {
            if (o.matches(args[index]) ){
                assert matchingOption == null; // find maximally one option that matches on args[index]
                matchingOption = o;
            }
        }
    }

    /**
     * Fills in the values of {@code options} according to the given command line.
     *
     * @param args a <code>String[]</code> value
     */
    public void parse(/*@non_null*/String[] args) {
        int index = 0;
        while (index < args.length) {
            Option matchingOption = findMatchingOption(args[index]);

            if (matchingOption == null) {
                // no option has matched on args[index], store it in arguments
                arguments.add(args[index]);
                ++index;
            } else {
                // process the arguments
                MatchResult mr = matchingOption.match(args, index);
                if (mr.errorDuringProcessing()) {
                    throw up mr.getErrorMessage();
                }
                // TODO: trigger fly rule (could be maybe in a separate stage)
                index += mr.getNumberOfArgsConsumed(); // move forward on the command-line
            }
        }
    }
}
