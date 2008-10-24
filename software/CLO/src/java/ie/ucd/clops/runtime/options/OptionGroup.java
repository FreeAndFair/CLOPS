package ie.ucd.clops.runtime.options;

import java.util.ArrayList;
import java.util.Collection;

public class OptionGroup implements IMatchable {

	Collection<IMatchable> options;
	
	private String identifier;

	public OptionGroup(String identifier) {
		options = new ArrayList<IMatchable>();
		this.identifier = identifier;
	}

	public void addOptionOrGroup( IMatchable option) {
		options.add( option);
	}

	/**
	 * Determines whether the given command line argumnet pertains to one
	 * of contained options or option groups.
	 */
	public Option getMatchingOption(/*@non_null*/String arg) {
		for (IMatchable option:options) {
		  Option o = option.getMatchingOption(arg);
		  if (o != null) {
		    return o;
		  }
		}
		return null;
	}

  public String getIdentifier() {
    return identifier;
  }

  @Override
  public String toString() {
    return "Option Group: \"" + getIdentifier() + "\"";
  }
  
  @Override
  public boolean equals(Object obj) {
    if (obj instanceof OptionGroup) {
      this.getIdentifier().equals(((OptionGroup)obj).getIdentifier());
    } else {
      return false;
    }
    return super.equals(obj);
  }

  @Override
  public int hashCode() {
    return getIdentifier().hashCode();
  }
	
}
