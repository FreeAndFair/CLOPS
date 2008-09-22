
/**
 * Internal representation of an automaton state.
 * @author Viliam Holub
 */
class State {
	/** Type of the state. */
	/*@ non_null @*/ StateType type;
	/** Name of the state, suppose to be Option. */
	final String name;
	/** Successors of the state. */
	State next1, next2;
	/** Stae index, used for effective generation of net-step lists. */
	int state_index;

	State( /*@ non_null @*/ StateType type,
			/*@ non_null @*/ final String name) {
		this.type = type;
		this.name = name;
	}

	/**
	 * Creates new state with specified fields.
	 * @param type type of the state
	 * @param name suppose to be Object
	 * @param next1 first successor
	 * @param next2 second successor
	 */
	State( /*@ non_null @*/ StateType type,
			/*@ non_null @*/ final String name,
			State next1, State next2) {
		this.type  = type;
		this.name  = name;
		this.next1 = next1;
		this.next2 = next2;
	}

	/** Add new successor state.
	 * @param s new succesor state
	 */
	void addNext( State s) {
		if (next1 == null)
			next1 = s;
		else
			next2 = s;
	}
}
