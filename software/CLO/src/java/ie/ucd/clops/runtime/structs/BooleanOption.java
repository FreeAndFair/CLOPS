package ie.ucd.clops.runtime.structs;

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

}