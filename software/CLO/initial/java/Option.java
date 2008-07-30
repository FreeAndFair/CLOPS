import java.util.ArrayList;
import java.util.Comparator;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

/**
 * Represents a command line option. Constructor and new options obtained by calling {@code registerOption}, 
 * which also stores the new option in a static collection.
 *
 * @author Mikolas Janota
 */

    class StrCmp implements Comparator<String> 
    {  public int compare(String s1, String s2) { return s1.compareTo(s2);}  }

/**
 * Describe class <code>Option</code> here.
 *
 * @author <a href="mailto:mikolas@functor-3.local">Mikoláš Janota</a>
 * @version 1.0
 */
public class Option {
    //@ private invariant \nonnullelements(names);
    private final /*@ non_null*/String[] names;

    //@ private static invariant options.elementType == \type(Option) && !options.containsNull;
    private static /*@ non_null*/ ArrayList<Option> options = new ArrayList<Option>();

    private static Map<String,Option> optionNamesMap = new HashMap<String,Option>();

    private static /*@ non_null*/ Comparator<String> stringComparator = new StrCmp();
        //String.CASE_SENSITIVE_ORDER;

    static {
       //@ set options.elementType = \type(Option);
    }

    /**
     * Returns an iterator over all registered options.
     */
    public static /*@non_null*/Iterable<Option> getOptions() {
        return options;
    }


    /*@ public normal_behavior
      @ requires \nonnullelements(names);
      @   ensures \fresh(\result); */
    /*@ also private behavior
      @   requires \nonnullelements(names);
      @   assignable options.objectState; 
      @   ensures options.contains(\result); 
      @   ensures \fresh(\result); */
    public static /*@ non_null*/Option registerOption(/*@ non_null*/String[] names) {
        Option newOption = new Option(names);
        options.add(newOption);
        for (String name : names) {
          optionNamesMap.put(name, newOption);
        }
        return newOption;
    }

    public static /*@ non_null*/Option registerOption(/*@ non_null*/String name) {
        return registerOption(new String[] { name });
    }


    /**
     * Searches for a registed option given one of its names.
     *
     * @param name the name of the option searched for
     * @return the option if foudn, <code>null</code> otherwise
     */
    //@ ensures \result != null ==> \result.isMe(name);
    public static Option findOption(/*@ non_null*/String name) {
        return optionNamesMap.get(name);
    }

    // Tests whether the given option has been registered.
    public /*@pure*/ static boolean isRegistered(/*@ non_null*/Option o) {
        return options.contains(o);
    }

    public /*@pure*/ /*@ non_null*/String toString() {
        if (names.length > 0) {
            return names[0];
        } else {
            return "<unspecified name>";
        }
    }

    public /*@pure*/ boolean equals(Object o) {
        return this == o;
    }

    /** Typed equivalent of the <code>equals</code> method. */
    public /*@pure*/ boolean isSame(Option o) {
        return this == o;
    }



    //@ requires \nonnullelements(names);
    private /*@pure*/ Option(/*@ non_null */String[] names) {
        this.names = (String[]) names.clone();
    }

    /**
     * Determines whether the given string is one of the names of this option.
     */
    public /*@pure*/ boolean isMe(/*@non_null*/String name) {
        //@ loop_invariant (\forall int x; 0 <= x & x < i; !(stringComparator.compare(names[x], name) == 0));
        for (int i = 0; i < names.length; i++) {
            if (stringComparator.compare(names[i], name) == 0) {
                return true;
            }
        }

        return false;
    }

}