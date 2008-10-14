/**
 * 
 */
package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.parser.MatchResult;

import java.util.Set;

/**
 * @author fintan
 *
 */
public abstract class BasicOption implements Option {

  private final Set<String> aliases;
  
  public BasicOption(final Set<String> aliases) {
    this.aliases = aliases;
  }
  
  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#getType()
   */
  public abstract OptionType getType();

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#getValue()
   */
  public abstract Object getValue();

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#hasValue()
   */
  public boolean hasValue() {
    // TODO Auto-generated method stub
    return false;
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#match(java.lang.String[], int)
   */
  public MatchResult match(String[] args, int offset) {
    String arg = args[offset];
    for (String alias : aliases) {
      if (arg.startsWith(alias)) {
        //return internalMatch?
        
      }
    }
    return MatchResult.negativeMatch();
  }
  
  protected abstract MatchResult handleMatched(final String[] args, final int offset);

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#set(java.lang.Object)
   */
  public abstract void set(Object value);

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#unset()
   */
  public abstract void unset();
  
}
