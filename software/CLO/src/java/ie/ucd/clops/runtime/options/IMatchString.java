package ie.ucd.clops.runtime.options;


/**
 * An interface that is used to obtain instances of 
 * the {@code IMatchable} interface from a {@code String}.
 *
 * @author Mikolas Janota
 */
public interface IMatchString  {

    /**
     * Obtain {@code IMatchable} associated with the given {@code String}.
     */
    IMatchable getMatchable(/*@non_null*/String param);
}

