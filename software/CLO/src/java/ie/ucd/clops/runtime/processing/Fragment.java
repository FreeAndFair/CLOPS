
package ie.ucd.clops.runtime.processing;

import java.util.*;

/**
 * A fragment of automaton.
 * A helper class used during automaton build. Last fragment becomes final
 * automaton.
 * For each fragment we store states with transitions heading outside.
 *
 * @author Viliam Holub
 */
class Fragment {
	/** Starting state. */
	State start;
	/** List of states of outgoing transitions. */
	LinkedList<State> out;

	/**
	 * Creates a fragment consisting of a single outputting state.
	 * @param start starting state, we create automaton with this state
	 */
	Fragment( /*@ non_null @*/ State start) {
		this.start = start;
		this.out = new LinkedList<State>();
		this.out.add( start);
	}

	/**
	 * Creates a fragment with one state and specified outputting states.
	 * @param state the starting state, we create autoamton with this state
	 * @param ll list of outgoing transitions (state they are heading to)
	 */
	Fragment( /*@ non_null @*/ State start, /*@ non_null @*/ LinkedList<State> out) {
		this.start = start;
		if (out != null)
			this.out = out;
		else
			this.out = new LinkedList<State>();
	}

	/**
	 * Creates a concatenation of this fragment and another fragment by
	 * modifying this fragment.
	 * @param f fragment of automaton we are concatenating
	 */
	Fragment concatenate( /*@ non_null @*/ final Fragment f) {
		for (State s:out)
			s.addNext( f.start);
		this.out = f.out;
		return this;
	}

	/**
	 * Assign the specified state as the one with outgoing transitions.
	 * @param s state with outgoing transition
	 */
	Fragment assignNext( /*@ non_null @*/ State s) {
		for (State sx:out)
			sx.addNext( s);
		return this;
	}

	/** Creates alternative between two fragments.
	 * A new starting state is created. We can continue either to the
	 * first or second fragment. Output states are joint.
	 * @param f1 left fragment of the alternative operator
	 * @param f2 right fragment of the alternative operator
	 */
	static Fragment alternative( /*@ non_null @*/ final Fragment f1,
			/*@ non_null @*/ final Fragment f2) {
		LinkedList<State> out = new LinkedList<State>( f1.out);
		out.addAll( f2.out);
		return new Fragment(
			new State( StateType.SPLIT, "", f1.start, f2.start),
			out);
	}

	/** Apply the plus operator to existing fragment.
	 * The execution continues to specified fragment. All the output from
	 * the fragment are transferred to our new state. We can continue from
	 * the state either to the fragment f or outside.
	 * @param f fragment the plus operator is applied to
	 */
	static Fragment plus( /*@ non_null @*/ Fragment f) {
		State s = new State( StateType.SPLIT, "", f.start, null);
		f.assignNext( s);
		LinkedList<State> out = new LinkedList<State>();
		out.add( s);
		return new Fragment( f.start, out);
	}

	/** Apply the star operator to existing fragment.
	 * We create a new fragment with a new state. From the state we can
	 * continue either to the specified fragment or outside.
	 * @param f fragment the star operator is applied to
	 */
	static Fragment star( /*@ non_null @*/ Fragment f) {
		State s = new State( StateType.SPLIT, "", f.start, null);
		f.assignNext( s);
		LinkedList<State> out = new LinkedList<State>();
		out.add( s);
		return new Fragment( s, out);
	}

	/** Apply the question mark operator to existing fragment.
	 * We create a new starting state, where we can continue either to the
	 * specified fragment or outside.
	 * @param f fragment the question mark operator is applied to
	 */
	static Fragment question( /*@ non_null @*/ Fragment f) {
		State s = new State( StateType.SPLIT, "", f.start, null);
		LinkedList<State> out = new LinkedList<State>( f.out);
		out.add( s);
		return new Fragment( s, out);
	}

	/** Apply the specified operator on a fragment.
	 * @param type token type, one of PLUS, STAR, QUESTION
	 */
	static Fragment apply_operator( /*@ non_null @*/ TokenType type,
			/*@ non_null @*/ Fragment f) {
		switch (type) {
			case PLUS: return plus( f);
			case STAR: return star( f);
			case QUESTION: return question( f);
		}
		return null;
	}
}
