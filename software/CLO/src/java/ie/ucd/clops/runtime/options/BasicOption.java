/**
 * 
 */
package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.parser.ProcessingResult;

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
  
  public Set<String> getAliases() {
    return aliases;
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
  public abstract ProcessingResult process(String[] args, int offset);

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#set(java.lang.Object)
   */
  public abstract void set(Object value);

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.Option#unset()
   */
  public abstract void unset();
  
}
