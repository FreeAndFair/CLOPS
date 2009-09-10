package ie.ucd.clops.runtime.options;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.Set;

/**
 * A class maintaining a collection of {@code IMatchable} objects and
 * implementing their retrieval.
 * @author Mikolas Janota
 */
public class MatchableCollection {
    /**
     * Enable a runtime check for duplicate matching.
     */
    public static final boolean assertForDuplicates = true;

    // collection of matchables
    protected Collection<IMatchable> ms;


    public MatchableCollection() {
        ms = new ArrayList<IMatchable>();
    }

    /**
     * Add a {@code IMatchable} object. An object must be added at most once.
     */
    protected void add(IMatchable m) {
        assert !ms.contains(m);
        ms.add(m);
    }

    /**
     * Obtain an {@code Option} associated with the given {@code String}.
     * If {@code assertForDuplicates} then assertion is triggered 
     * if more than one {@code Option} matched. 
     *  the option had to be added via 
     *  {@link ie.ucd.clops.runtime.options.MatchableCollection#add}
     */
    public Option<?> getMatchingOption(String argString, int index) {
        ArrayList<Option<?>> matched = new ArrayList<Option<?>>(1);
        for (IMatchable m : ms) {
            Option<?> foundM = m.getMatchingOption(argString, index);
            if (foundM != null) matched.add(foundM);
        }
        if (matched.isEmpty()) return null;
        assert !assertForDuplicates || matched.size() == 1;
        return matched.get(0);
    }

    public Set<Option<?>> getAllOptions() {
      Set<Option<?>> result = new HashSet<Option<?>>();
      for (IMatchable m : ms) {
        result.addAll(m.getAllOptions());
      }
      return result;
    }

    @Override
    public boolean equals(Object o) {
      if (o instanceof MatchableCollection) {
        MatchableCollection omc = (MatchableCollection) o;
        return omc.ms.equals(this.ms);
      } else {
        return false;
      }
    }

    @Override 
    public int hashCode() {
        return ms.hashCode();
    }
    
    public boolean hasAtLeastOneOptionWithValue() {
      for (IMatchable matchable : ms) {
        if (matchable.hasAtLeastOneOptionWithValue()) {
          return true;
        }
      }
      return false;
    }
}

