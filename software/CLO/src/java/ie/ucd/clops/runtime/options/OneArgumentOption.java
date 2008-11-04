package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.parser.ProcessingResult;

import java.util.Set;

/**
 * Option that requires one argument.
 * Either -op1=value or ... -op1 value ...
 * 
 * @author Fintan
 *
 */
public abstract class OneArgumentOption extends BasicOption {

  public OneArgumentOption(String identifier, Set<String> aliases) {
    super(identifier, aliases);
  }

  public OneArgumentOption(String identifier) {
    super(identifier);
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#match(java.lang.String[], int)
   */
  public ProcessingResult process(String[] args, int offset) {
    String currentArg = args[offset];
    assert this.getMatchingOption(currentArg) == this;
    String alias = getMatchingAlias(currentArg);
    try {
      //If we allow -arg=VALUE
      if (currentArg.length() > alias.length() && currentArg.charAt(alias.length()) == '=') {
        // -arg=VALUE format
        setFromString(currentArg.substring(alias.length() + 1));
        return ProcessingResult.successfulProcess(1);
      } else {
        // Next parameter
        if (offset >= args.length)
          return ProcessingResult.erroneousProcess( "Parameter expected");
        setFromString( args[offset+1]);
        return ProcessingResult.successfulProcess(2);
      }
    }
    catch (InvalidOptionValueException iove) {
      return ProcessingResult.erroneousProcess(iove.getMessage());
    }
  }
  
}
