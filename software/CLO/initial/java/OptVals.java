import java.util.*;

/** 
 * A class representing the setting of options, their values and positions. 
 */
public class OptVals {
    Map<Option, Boolean> vals = new HashMap<Option, Boolean>();
    Map<Option, Integer> positions = new HashMap<Option, Integer>();
    int position = 0;

    /** Copy constructor */
    /*@pure*/ public OptVals(OptVals other) {
        this.vals = new HashMap<Option, Boolean>(other.vals);
        this.positions = new HashMap<Option, Integer>(other.positions);
        this.position = other.position;
    }

    /** Initializes a new class with the given list of options. */
    /*@pure*/public OptVals(List<Option> opts) {
        for (int i = 0; i < opts.size(); i++) {
            vals.put(opts.get(i), true);
            positions.put(opts.get(i), i);
        }
        position = opts.size();
    }


    /** Sets the given options to the given value. Its position is the last in order. */
    public void set(Option o, boolean val) {
        positions.put(o, position);
        vals.put(o, val);
        ++position;
    }


    /** Determines whether {@code o1} was set before {@code o2}. */
    /*@pure*/ public boolean before(Option o1, Option o2) {
        Integer p1 = positions.get(o1);
        Integer p2 = positions.get(o2);
        if (p1 == null || p2 == null) return false;
        return p1 < p2;
    }

    /** Determines whether {@code opt} has the value {@code val}. */
     /*@pure*/ public boolean isVal(Option opt, boolean val) {
        Boolean oVal = vals.get(opt);
        return oVal != null && oVal == val;
    }

    /** Determines whether {@code opt} has the value {@code true}. */
     /*@pure*/ public boolean isTrue(Option opt) {
        return isVal(opt, true);
    }

    /** Determines whether {@code opt} has the value {@code false}. */
     /*@pure*/ public boolean isFalse(Option opt) {
        return isVal(opt, true);
    }

    public boolean equals(Object other) {
        OptVals ov = (OptVals) other;
        return ov.vals.equals(this.vals) && ov.positions.equals(this.positions);
    }

    public int hashCode() {
        return vals.hashCode() ^ positions.hashCode();
    }
}
