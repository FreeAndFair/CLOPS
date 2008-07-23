import java.util.*;

/**
 * An interface that provides a so-called override function, which returns
 * an overriding value for the given option under the given values of options. 
 * Returns {@cod null} if there is no such overriding value.
 */
public interface IOverride {
    public Boolean getOverride(OptVals vals, Option opt);
}