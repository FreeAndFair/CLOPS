package ie.ucd.clops.runtime.options;


/**
 * A base class for all structures that are used to describe
 * option states in the runtime. 
 */
public interface IMatchable {
  
  public Option getMatchingOption(String argument);
  
}
