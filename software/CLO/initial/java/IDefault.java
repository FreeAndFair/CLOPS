import java.util.*;

/**
 * An interface that provides a so-called default function, which returns 
 * a default value for the given option under the given values of options. 
 * Returns {@cod null} if there is no default value.
 */
public interface IDefault {
    public Boolean getDefault(OptVals vals, Option opt);
}

