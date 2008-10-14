package ie.ucd.clops.runtime.options;

import java.util.*;

/**
 * A base class for all structures that are used to describe
 * option states in the runtime. 
 * Plus pertaining functionality, such as parsing of arguments.
 *
 */
public interface IMatchable {
    /**
     * Determines whether the given command line argumnet pertains to this option.
     */
    public boolean doIMatch(/*@non_null*/String arg);

    /**
     * Determines whether the given option matches.
     */
    public boolean doIMatch(/*@non_null*/Option o);


    /**
     * Returns add options it represents.
     */
    public ArrayList<Options> getOptions();
}
