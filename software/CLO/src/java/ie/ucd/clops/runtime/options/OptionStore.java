package ie.ucd.clops.runtime.options;

import java.io.PrintStream;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Set;

/**
 * A class for storing options, implementing a retrival function from Strings to options. 
 *
 * @author Mikolas Janota
 * @author Fintan
 */
public class OptionStore implements IMatchString  {
  
   private final HashMap<String, Option> identifierOptionMap;
   private final HashMap<String, Option> aliasOptionMap;
   private final HashMap<String, IMatchable> identifierMatchableMap;
   private final HashSet<Option> options;

   /**
    * Create a new OptionStore. 
    */
   public OptionStore() {
     identifierOptionMap = new HashMap<String, Option>();
     aliasOptionMap = new HashMap<String, Option>();
     identifierMatchableMap = new HashMap<String, IMatchable>();
     options = new HashSet<Option>();
   }
   
   /**
    * Add an option to this store.
    */
   public void addOption(/*@non_null*/Option o) {
      assert !options.contains(o);
      options.add(o);
      
      assert !identifierMatchableMap.containsKey(o.getIdentifier());
      identifierMatchableMap.put(o.getIdentifier(), o);
      
      assert !identifierOptionMap.containsKey(o.getIdentifier());
      identifierOptionMap.put(o.getIdentifier(), o);
      
      for (String alias : o.getAliases()) {
         assert !aliasOptionMap.containsKey(alias); // TODO: should be reported
         aliasOptionMap.put(alias, o);
      }
   }
   
   /**
    * Add an option group to this option store
    * @param og
    */
   public void addOptionGroup(/*@non_null*/OptionGroup og) {
     assert !identifierMatchableMap.containsKey(og.getIdentifier());
     identifierMatchableMap.put(og.getIdentifier(), og);
   }

   /**
    * Obtain the set of options in this store.
    */
   public Set<Option> getOptions() {
      return options;
   }

  /* (non-Javadoc)
   * @see ie.ucd.clo.runtime.options.IMatchString#getMatchable(java.lang.String)
   */  
   public IMatchable getMatchable(String param) {
      return identifierMatchableMap.get(param);
   }

   /**
    * Get the Option from this store with the provided identifier,
    * if one is present (null otherwise).
    * @param identifier the identifier to the Option to get.
    * @return the Option with this identifier, or null.
    */
   public Option getOptionByIdentifier(String identifier) {
     return identifierOptionMap.get(identifier);
   }
   
   /**
    * Get the Option that has the provided alias, if one is present
    * (null otherwise).
    * @param alias the alias to the Option to get.
    * @return the Option with this alias, or null.
    */
   public Option getOptionByAlias(String alias) {
     return aliasOptionMap.get(alias);
   }
    
   @Override
   public String toString() {
     StringBuilder sb = new StringBuilder();
     for (Option op : options) {
       if (op.hasValue()) {
         sb.append(op.toString());
         sb.append(", ");
       }
     }
     return sb.toString();
   }
}

