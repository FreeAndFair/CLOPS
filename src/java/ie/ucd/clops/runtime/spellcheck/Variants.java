package ie.ucd.clops.runtime.spellcheck;

import java.util.Iterator;
import java.util.List;
import java.util.ArrayList;
import java.util.Set;
import java.util.HashSet;


/**
 * Generates edit variants of a given string. It is meant to be used
 * as an iterator. The generated edits go in the order of distance
 * from the beginning of the string, i.e., edits at position 0 come
 * first.
 * @author Mikolas Janota
 */
public class Variants implements Iterator<String> {
    // the original string being modified
    private final String str;

    // the set of letters that are considered
    // for overwriting and inserting
    private List<Character> changeLetters;

    //up to where we are making changes
    private final int maxIndex;

    // where is the string currently being edited a.k.a cursor
    private int i;

    // precomputed suffixes of {@code str} from index (inclusive)
    private String[] suffixes;
    // precomputed prefixes of {@code str} up to index (exclusive)
    private String[] prefixes;


    private static final boolean debug=false;

    /** Initialize the iterator with a given String. */
    /*@pure*/public Variants(final String str) {
        this.i=0;// start changes at 0
        this.str=str;

        // initialize suffixes and prefixes
        maxIndex=str.length()-1;
        suffixes=new String[maxIndex+2];
        prefixes=new String[maxIndex+2];
        for (int i=0; i<=(maxIndex+1); i++) {
            if (i >= str.length()) {
                suffixes[i]="";
                prefixes[i]=str;
            } else {
                suffixes[i]=str.substring(i,str.length());
                prefixes[i]=str.substring(0,i);
            }
        }

        // initialize change letters
        changeLetters=new ArrayList<Character>(52);
        for (char c='a'; c <='z'; c++) changeLetters.add(c);
        for (char c='A'; c <='Z'; c++) changeLetters.add(c);
    }

    Set<String> edits=new HashSet<String>(0);

    public boolean hasNext() {
        return i<=maxIndex || !edits.isEmpty();
    }

    public String next() { 
        if (edits.isEmpty()) {
            // compute changes as the cursor
            edits=getCurrentEdits();
            if (debug) System.out.println("edits at " + i + " " + edits);
            // move the cursor
            ++i;
        }
        String r=edits.iterator().next();
        edits.remove(r);
        return r;
    }

    /** Should not be called doesn't do anything except for assert.*/
    public void remove() {assert false;}

    /** Generates edits at {@code index}. */
    //@ ensures \fresh(\result);
    /*@pure*/private Set<String> getCurrentEdits() {
        Set<String> retv=new HashSet<String>(60);
        assert i<= maxIndex;
        // overwrite and inserts
        for (Character c : changeLetters) 
            retv.add(prefixes[i] + c + suffixes[i]);
        // swap
        if (i < maxIndex) 
            retv.add(prefixes[i] + 
                     str.charAt(i+1) + str.charAt(i) + 
                     suffixes[i+2]);
        
        // delete
        retv.add(prefixes[i]+suffixes[i+1]);
        
        // inserts
        for (Character c : changeLetters) 
            retv.add(prefixes[i] + c + suffixes[i+1]);

        // inserts the last character
        if (i==maxIndex) 
            for (Character c : changeLetters) 
                retv.add(prefixes[maxIndex+1] + c + 
                         suffixes[maxIndex+1]);

        return retv;
    }

    //test run ================================================
    public static void main(String[] a) {
        Variants v=new Variants("abc");
        v.changeLetters=new ArrayList<Character>(2);
        for (char c='x'; c <='y'; c++) v.changeLetters.add(c);
        System.out.println("running variants with  modif alphabet " + 
                           v.changeLetters);
        while (v.hasNext()) 
            System.out.println(v.next());
    }
}
