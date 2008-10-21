package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.options.IMatchable;
import java.util.*;

/**
 * A class for storing options, implementing a retrival function from Strings to options. 
 *
 * @author Mikolas Janota
 */
public class OptionStore implements IMatchString  {
  
   private final HashMap<String, Option> identifierOptionMap;
   private final HashMap<String, Option> aliasOptionMap;
   private final HashMap<String, IMatchable> identifierMatchableMap;
   private final HashSet<Option> options;

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

   public Option getOptionByIdentifier(String identifier) {
     return identifierOptionMap.get(identifier);
   }
   
   public Option getOptionByAlias(String alias) {
     return aliasOptionMap.get(alias);
   }
    
}

