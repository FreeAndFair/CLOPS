import java.util.*;

/**
 * An interface that provides a so-called default function.
 */
public interface IDefault {

    /**
     * Returns a default value for the given option and option values.
     * The value of {@code opt} in {@code vals} should be ignored by this function.
     * @param vals the values of the other options set so far
     * @param opt the option for which the default should be computed
     * @return {@code null} iff the there is no default value
     */
    public /*@pure*/ /*@nullable*/ Boolean getDefault(/*@non_null*/OptVals vals, /*@non_null*/Option opt);
}

