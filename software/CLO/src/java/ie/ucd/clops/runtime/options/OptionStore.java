package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.options.IMatchable;
import java.util.*;

/**
 * A class for storing options, implementing a retrival function from Strings to options. 
 *
 * @author Mikolas Java
 */
public class OptionStore implements IMatchString  {
   private HashMap<String, Option> m = new HashMap<String, Option>();
   private HashSet<Option> s = new HashSet<Option>();

   /**
    * Add an option to this store.
    */
   public void addOption(/*@non_null*/BasicOption o) {
      assert !s.contains(o);
      s.add(o);
      for (String alias : o.getAliases()) {
         assert m.get(alias) == null; // TODO: should be reported
         m.put(alias, o);
      }
   }

   /**
    * Add an option to this store.
    */
   public Set<Option> getOptions() {
      return s;
   }

   /**
    * Add an option to this store.
    */
   public IMatchable getMatchable(String param) {
      return m.get(param);
   }

}

