import java.util.*;

/**
 * An abstract class corresponding to the {@code IConstraint} interface.
 * @author Mikolas Janota
 */
public abstract class Constraint implements IConstraint {
    abstract public boolean isValid(OptVals vals);

    /**
     * Computes an and over the given constraints.
     */
    public static /*@non_null*/Constraint and(final /*@non_null*/ Iterable<Constraint> constraints) {
        return new Constraint() {
            final Iterable<Constraint> cs = constraints;
            public boolean isValid(OptVals vals) {
                for (Constraint c : cs) {
                    if (!c.isValid(vals)) return false;
                }
                return true;
            }
        };
    }
}