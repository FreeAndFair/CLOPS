package ie.ucd.clops.runtime.options;

import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

/**
 * A class for storing options, implementing a retrieval function from Strings to options. 
 *
 * @author Mikolas Janota
 * @author Fintan
 */
public class OptionStore extends MatchableCollection 
implements IMatchString  {

  private final HashMap<String, Option<?>> identifierOptionMap;
  private final HashMap<String, IMatchable> identifierMatchableMap;
  private final HashSet<Option<?>> options;

  /**
   * Create a new OptionStore. 
   */
  public OptionStore() {
    identifierOptionMap = new HashMap<String, Option<?>>();
    identifierMatchableMap = new HashMap<String, IMatchable>();
    options = new HashSet<Option<?>>();
  }


  protected void addMatchable(IMatchable m) {
    assert !identifierMatchableMap.containsKey(m.getIdentifier());
    identifierMatchableMap.put(m.getIdentifier(), m);
    add(m);
  }

  /**
   * Add an option to this store.
   */
  public void addOption(/*@non_null*/Option<?> o) {
    assert !options.contains(o);
    options.add(o);

    assert !identifierOptionMap.containsKey(o.getIdentifier());
    identifierOptionMap.put(o.getIdentifier(), o);

    addMatchable(o);
  }

  /**
   * Add an option group to this option store.
   */
  public void addOptionGroup(/*@non_null*/OptionGroup og) {
    addMatchable(og);
  }

  /**
   * Obtain the set of options in this store.
   */
  public Set<Option<?>> getOptions() {
    return options;
  }

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.IMatchString#getMatchable(java.lang.String)
   */  
  public IMatchable getMatchable(String param) {
    return identifierMatchableMap.get(param);
  }

  /**
   * Get the Option from this store with the provided identifier,
   * if one is present (null otherwise).
   * @param identifier the identifier to the Option to get.
   * @return the Option with this identifier, or null.
   */
  public Option<?> getOptionByIdentifier(String identifier) {
    return identifierOptionMap.get(identifier);
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    for (Option<?> op : options) {
      if (op.hasValue()) {
        sb.append(op.toString());
        sb.append(", ");
      }
    }
    return sb.toString();
  }
}

