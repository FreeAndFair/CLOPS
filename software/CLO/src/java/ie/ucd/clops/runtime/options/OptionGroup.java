package ie.ucd.clops.runtime.options;

import java.util.ArrayList;
import java.util.Collection;

public class OptionGroup implements IMatchable {

	Collection<IMatchable> options;

	public OptionGroup() {
		options = new ArrayList<IMatchable>();
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
	
}
