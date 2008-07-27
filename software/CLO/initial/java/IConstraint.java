import java.util.*;

/**
 * An interface that provide so-called validity function.
 *
 * @author Mikolas Janota
 */
public interface IConstraint {
    /**
     * Determines whether the given option values are valid.
     */
    public /*@pure*/ boolean isValid(/*@non_null*/OptVals vals);
}