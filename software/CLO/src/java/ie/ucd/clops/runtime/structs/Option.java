package ie.ucd.clops.runtime.structs;

import ie.ucd.clops.dsl.structs.OptionDescription;

/**
 * A base class for all structures that are used to describe
 * option states in the runtime. 
 * Plus pertaining functionality, such as parsing of arguments.
 *
 */
public abstract class Option {
    /**
     * Static information about this option.
     */
    public abstract /*@non_null*/OptionDescription getDescription();


    // TODO: should doIMatch be collapsed into parseMyself(...)==0
    /**
     * Determines whether the given command line argumnet pertains to this option.
     */
    public boolean doIMatch(/*@non_null*/String arg) { return getDescription().isAlias(arg); }
    

    /**
     * Fill in this option according to the command line arguments.
     *
     * @param args command line arguments in their raw form
     * @param position the currecnt position of parsing
     * @return number of arguments parsed
     */
    //@ requires position >= 0;   
    //@ ensures \result >= 0;
    public abstract int parseMyself(/*@non_null*/String[] args, int position);


    /**
     * Determines whether this option is not in an undefined state.
     */
    public abstract boolean hasValue();


    /**
     * Brings the option into the undefined state.
     */
    public abstract void unset();


    /**
     * Matches arguments if any.
     * @param args arguments on command line
     * @param index index in the command line, first argument of the option
     */
    public abstract MatchResult match( String[] args, int index);
}
