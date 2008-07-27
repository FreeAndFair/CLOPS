import java.util.*;

/**
 * An interface that provides a so-called override function.
 */
public interface IOverride {

    /**
     * Determines the value that should override the current value of the given option under 
     * the given values of other options.
     *
     * @param vals the values of other options, the value of {@code opt} should be ignored
     * @param opt the option whose value should be overriden
     * @return the overriding value, {@code null} iff  {@code opt} should not be overriden
     */
    public /*@pure*/ Boolean getOverride(/*@non_null*/OptVals vals, /*@non_null*/Option opt);
}