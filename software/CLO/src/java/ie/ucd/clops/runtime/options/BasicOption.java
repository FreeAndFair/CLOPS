/**
 * 
 */
package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.parser.ProcessingResult;

import java.util.HashSet;
import java.util.Set;

/**
 * @author Fintan
 *
 */
public abstract class BasicOption implements Option {

  private final Set<String> aliases;
  private final String identifier;
  
  public BasicOption(String identifier, final Set<String> aliases) {
    this.identifier = identifier;
    this.aliases = aliases;
  }
  
  public BasicOption(String identifier) {
    this(identifier, new HashSet<String>());
  }
  
  public Set<String> getAliases() {
    return aliases;
  }
  
  public void addAlias(String alias) {
    aliases.add(alias);
  }
  
  /* (non-Javadoc)
   * @see ie.ucd.clops.runtime.options.IMatchable#getIdentifier()
   */
  public String getIdentifier() {
    return identifier;
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
