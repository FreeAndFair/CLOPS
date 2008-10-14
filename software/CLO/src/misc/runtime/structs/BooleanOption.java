package ie.ucd.clops.runtime.structs;

import ie.ucd.clops.dsl.structs.OptionDescription;

/**
 * Generic class capturing Runtime information about boolean options.
 *
 */
public class BooleanOption extends Option {
    Boolean value = null;

    public int parseMyself(/*@non_null*/String[] args, int position) {
        value = true;
        return 1;
    }

    public boolean hasValue() { return value != null; }
    public void unset() { value = null; }

    public boolean getValue() { return value; }
    public void setValue(Boolean newValue) { value = newValue; }

    /**
     * Matches arguments if any.
     * @param args arguments on command line
     * @param index index in the command line, first argument of the option
     * TODO: empty; to make cimpiler happy
     */
    public MatchResult match( String[] args, int index) {
        // TODO
    	return null;
    }

    /**
     * Static information about this option.
     * TODO: empty; to make cimpiler happy
     */
    public /*@non_null*/OptionDescription getDescription() {
    	return null;
    }
}
