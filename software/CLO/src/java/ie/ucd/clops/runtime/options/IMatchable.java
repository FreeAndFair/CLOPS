package ie.ucd.clops.runtime.options;


/**
 * A base class for all structures that are used to describe
 * option states in the runtime. 
 */
public interface IMatchable {
  
  public static final char SEP = '\0';
  public static final String SEP_STRING = SEP + "";
  
  String getIdentifier();
  
  Option<?> getMatchingOption(String argumentString, int index);
  
}
