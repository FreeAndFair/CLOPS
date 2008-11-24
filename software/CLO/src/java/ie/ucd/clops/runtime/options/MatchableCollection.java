package ie.ucd.clops.runtime.options;

import java.util.*;

/**
 * A class maintaining a collecgtion of {@code IMatchable} objects and
 * implementing their retrieval.
 * @author Mikolas Janota
 */
public class MatchableCollection {
    /**
     * Enable a runtime check for duplicate matching.
     */
    public static boolean assertForDuplicates = true;

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
     * If {@code assertForDuplicates} then asertion is triggered 
     * if more than one {@code Option} matched.
     * @return an option associated with the given {@code s}, 
     *  the option had to be added via 
     *  {@link ie.ucd.clops.runtime.options.MatchableCollection#add}
     */
    public Option<?> getMatchingOption(String s) {
        ArrayList<Option<?>> matched = new ArrayList<Option<?>>(1);
        for (IMatchable m : ms) {
            Option<?> foundM = m.getMatchingOption(s);
            if (foundM != null) matched.add(foundM);
        }
        if (matched.isEmpty()) return null;
        assert !assertForDuplicates || matched.size() == 1;
        return matched.get(0);
    }

    @Override
    public boolean equals(Object o) {
        MatchableCollection omc = (MatchableCollection) o;
        return omc.ms.equals(this.ms);
    }

    @Override 
    public int hashCode() {
        return ms.hashCode();
    }
}

