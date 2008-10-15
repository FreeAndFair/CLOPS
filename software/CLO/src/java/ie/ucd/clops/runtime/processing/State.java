
package ie.ucd.clops.runtime.processing;


/**
 * Internal representation of an automaton state.
 * @author Viliam Holub
 */
class State<T> {
	/** Type of the state. */
	/*@ non_null @*/ StateType type;
	/** Matchable interface for states that may match. */
	T match;
	/** Successors of the state. */
	State<T> next1, next2;
	/** State index, used for effective generation of net-step lists. */
	int state_index;

	State( /*@ non_null @*/ StateType type,
			/*@ non_null @*/ T match) {
		this.type = type;
		this.match = match;
	}

	/**
	 * Creates new state with specified fields.
	 * @param type type of the state
	 * @param match matchable interface if the state is matchable
	 * @param next1 first successor
	 * @param next2 second successor
	 */
	State( /*@ non_null @*/ StateType type,
			/*@ non_null @*/ T match,
			State<T> next1, State<T> next2) {
		this.type  = type;
		this.match  = match;
		this.next1 = next1;
		this.next2 = next2;
	}

	/** Add new successor state.
	 * @param s new succesor state
	 */
	void addNext( State<T> s) {
		if (next1 == null)
			next1 = s;
		else
			next2 = s;
	}
}
