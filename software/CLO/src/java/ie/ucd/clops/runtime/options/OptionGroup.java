package ie.ucd.clops.runtime.options;

import java.util.*;

public class OptionGroup implements IMatchable {

	Collection<IMatchable> options;

	public OptionGroup() {
		options = new ArrayList<IMatchable>();
	}

	public void addOptionGroup( IMatchable option) {
		options.add( option);
	}

	/**
	 * Determines whether the given command line argumnet pertains to one
	 * of contained options or option groups.
	 */
	public boolean doIMatch(/*@non_null*/String arg) {
		for (IMatchable option:options)
			if (option.doIMatch( arg))
				return true;
		return false;
	}

	/**
	 * Determines whether the given option is in the container.
	 * @param o option to match
	 */
	public boolean doIMatch(/*@non_null*/Option o) {
		for (IMatchable option:options)
			if (option.doIMatch( o))
				return true;
		return false;
	}

	/**
	* Returns add options it represents.
	*/
	public ArrayList<Options> getOptions() {
		ArrayList<Options> list = new ArrayList<Options>();
		for (IMatchable option:options)
			list.addAll( option.getOptions());
		return list;
	}
}
