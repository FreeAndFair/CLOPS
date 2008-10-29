
package ie.ucd.clops.runtime.automaton;

/*
 * The implementation slighty follows the reg-exp NDA implementation at
 * http://swtch.com/~rsc/regexp/
 */

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Stack;



/**
 * Represents format of the command line as an automaton and allows traversing
 * the automaton with options.
 *
 * @author Viliam Holub
 */
public class Automaton<T> {

	/*
	 * Automaton fields
	 */

	/** Step serial number.
	 * Step number is used for effective creation of the list of active
	 * states. */
	int step_index;
	/** Indication of error state.
	 * If this variable is set, we are in the error state. */
	boolean error;
	/** Starting state of the automaton. */
	State<T> /*@ non_null @*/ start_state;
	/** List of active states.
	 * The list is updated every step. */
	ArrayList<State<T>> /*@ non_null @*/ arr;
	/** Backup of active states.
	 * The backup is used for error reporting only. */
	ArrayList<State<T>> /*@ non_null @*/ arr_backup;


	/*
	 * Code
	 */

	/** Creates automaton representation of command line format.
	 */
	//@ tokens.size() != 0;
	public Automaton( /*@ non_null @*/ List<Token<T>> tokens)
			throws RightOpenBracketException, LeftOpenBracketException,
			OpenQuestionException, EmptyAlternativeException,
			OpenStarException, OpenPlusException {
		arr = arr_backup = new ArrayList<State<T>>();
		step_index = 1;
		error = false;

		build( tokens);
		addSuccessors( start_state, arr);
		step_index++;
	}

	/**
	 * Context class used for format parsing and automation building.
	 */
	private class Context {
		int alternatives; // Level of alternatives "|"
		int atoms; // Number of atoms (options to concatenate)
	}

	/**
	 * Builds automaton from the list of tokens.
	 */
	//@ tokens.size() != 0;
	private void build( /*@ non_null @*/ List<Token<T>> tokens)
			throws RightOpenBracketException, LeftOpenBracketException,
			OpenQuestionException, EmptyAlternativeException,
			OpenStarException, OpenPlusException {
		// Stack of contexts, each context represents nested ()
		Stack<Context> ctxs = new Stack<Context>();
		// Fragments of automaton
		Stack<Fragment<T>> fragments = new Stack<Fragment<T>>();
		// Current context
		Context ctx = new Context();

		for (Token<T> t:tokens) switch (t.type) {
			case MATCH:
				// If there are two atom fragments on stack, concatenate
				if (ctx.atoms > 1) {
					Fragment<T> f = fragments.pop();
					fragments.peek().concatenate( f);
					ctx.atoms--;
				}
				// Create fragment that matches the given string
				// Push fragment into stack
				fragments.push( new Fragment<T>( new State<T>( StateType.MATCH, t.match)));
				ctx.atoms++;
				break;
			case LEFT:
				// Concatenate atoms on stack
				if (ctx.atoms > 1) {
					Fragment<T> f = fragments.pop();
					fragments.peek().concatenate( f);
					ctx.atoms--;
				}
				// Save context and create a new one
				ctxs.push( ctx);
				ctx = new Context();
				break;
			case RIGHT:
				// Test if right bracket without left one
				if (ctxs.size() == 0)
					throw new RightOpenBracketException();
				
				// If there are no atoms, syntax error -- ok if alternatives != 0
				if (ctx.atoms == 0) {
					throw new RightOpenBracketException();
				}
				// Concatenate atoms on stack
				if (ctx.atoms > 1) {
					Fragment<T> f = fragments.pop();
					fragments.peek().concatenate( f);
					ctx.atoms--;
				}
				// Create alternatives from fragments on stack
				if (ctx.alternatives > 0) {
					if (fragments.size() == 1)
						throw new EmptyAlternativeException();
					fragments.push( Fragment.alternative(
						fragments.pop(), fragments.pop()));
				}
				// Recover old context
				ctx = ctxs.pop();
				ctx.atoms++;
				break;
			case OR:
				if (ctx.atoms == 0 && ctx.alternatives != 0) {
					// Use of multiple alternatives ||
					// Ignore this one
					break;
				}
				if (ctx.atoms == 0 && ctx.alternatives == 0) {
					// If there are no fragments, raise error
					throw new EmptyAlternativeException();
				}
				
				// Concatenate fragments on stack
				while (ctx.atoms>1) {
					// Concatenate two fragments
					Fragment<T> f = fragments.pop();
					fragments.peek().concatenate( f);
					ctx.atoms--;
				}
				// Continue to make alternatives...
				if (ctx.alternatives > 0) {
					fragments.push( Fragment.alternative(
						fragments.pop(), fragments.pop()));
				}
				// Set status of alternatives
				ctx.alternatives = 1;
				ctx.atoms = 0;
				break;
			case PLUS:
				// If there are no atom fragments, raise error
				if (ctx.atoms == 0) throw new OpenPlusException();
				// Apply operator to the last fragment
				fragments.push( Fragment.apply_operator( TokenType.PLUS, fragments.pop()));
				break;
			case STAR:
				// If there are no atom fragments, raise error
				if (ctx.atoms == 0) throw new OpenStarException();
				// Apply operator to the last fragment
				fragments.push( Fragment.apply_operator( TokenType.STAR, fragments.pop()));
				break;
			case QUESTION:
				// If there are no atom fragments, raise error
				if (ctx.atoms == 0) throw new OpenQuestionException();
				// Apply operator to the last fragment
				fragments.push( Fragment.apply_operator( TokenType.QUESTION, fragments.pop()));
				break;
		}

		// Report error if there are unclosed brackets
		if (ctxs.size() != 0)
			throw new LeftOpenBracketException();
		
		// If the stack is empty, comply
		if (fragments.size() == 0) {
			// TODO
		}
		// Concatenate any residual atoms
		if (ctx.atoms > 1) {
			Fragment<T> f = fragments.pop();
			fragments.peek().concatenate( f);
		}
		// If there is unclosed alternative, close it
		if (ctx.alternatives != 0) {
			if (fragments.size() == 1)
				throw new EmptyAlternativeException();
			fragments.push( Fragment.alternative(
					fragments.pop(), fragments.pop()));
		}
		// Create final fragment
		State<T> s = new State<T>( StateType.END, null, null, null);
		Fragment<T> fin = fragments.pop();
		fin.assignNext( s);
		
		assert fragments.isEmpty();

		// Write start state
		start_state = new State<T>( StateType.SPLIT, null, fin.start, null);
	}

	/** Adds successors of s which has the type MATCH or END.
	 * To avoid duplicates in the output list (and avoid cycling as well),
	 * we update each state with step index and add only those, which state
	 * index is less than the current one.
	 * @param state state to add or follow
	 * @param successors output list of states
	 */
	private void addSuccessors2(
			/*@ non_null @*/ State<T> state,
			/*@ non_null @*/ List<State<T>> successors) {
		if (state == null || state.state_index == step_index)
			return;
		state.state_index = step_index;
		if (state.type == StateType.SPLIT) {
			addSuccessors2( state.next1, successors);
			addSuccessors2( state.next2, successors);
		} else {
			successors.add( state);
		}
	}

	/** Adds successors of s of the type MATCH or END to the list.
	 * Type of the state s must by MATCH or END.
	 * @param state state to follow
	 * @param successors output list of states
	 */
	private void addSuccessors(
			/*@ non_null @*/ State<T> state,
			/*@ non_null @*/List<State<T>> successors) {
		if (state.state_index == step_index)
			return;
		addSuccessors2( state.next1, successors);
		addSuccessors2( state.next2, successors);
		state.state_index = step_index;
	}

	/** Tests if the current state matched with the token, follows outgoing
	 * transitions if so and saves successor states.
	 * @param state state to follow
	 * @param transition_labels a collection of transition labels to process
	 * @param add list of successor states
	 */
	private void follow(
			/*@ non_null @*/ State<T> state,
			/*@ non_null @*/ Collection<T> transition_labels,
			/*@ non_null @*/ List<State<T>> arr) {

		// Type of the state must be ready to match.
		if (state.type != StateType.MATCH)
			return;
		// Follow all the transition labels.
		for (T transition_label:transition_labels) {
			if (state.match.equals(transition_label)) {
				// We have a match, add succesors
				addSuccessors( state, arr);
			}
		}
	}

	/** Apply next step in automaton.
	 * @param o collection of transition labels to process
	 * @return true if we could follow at least one of the transition labels
	 */
	public boolean nextStep( /*@ non_null @*/ Collection<T> o) {
		// Do not continue if we are in an error state
		if (error)
			return false;

		// Process next step, store states
		ArrayList<State<T>> arr2 = new ArrayList<State<T>>();
		for (State<T> s:arr)
			follow( s, o, arr2);
		arr_backup = arr;
		arr = arr2;

		// Update step
		step_index++;

		// If the final list of state is empty, we are in the error
		// state
		error = arr2.isEmpty();

		return !error;
	}

	/** Apply next step in automaton.
	 * @param transition transition label to process
	 * @return true if we could follow that transition label
	 */
	public boolean nextStep( /*@ non_null @*/ T transition) {
		List<T> l = new LinkedList<T>();
		l.add( transition);
		return nextStep( l);
	}

	/** Returns true if the automaton is accepting.
	 * Automaton is accepting if at least one of the current automaton
	 * states is accepting.
	 *
	 * @return true if the automaton is accepting
	 */
	public boolean isAccepting() {
		for (State<T> s:arr) {
			if (s.type == StateType.END)
				return true;
		}
		return false;
	}

	/** Returns in the automaton is in error state.
	 * @return true if the automaton is in error state
	 */
	public boolean inErrorState() {
		return error;
	}
	
	/** Returns list of available transitions.
	 * @return list of available trantions
	 */
	//@ ensures \return != null;
	public List<T> availableTransitions() {
		List<T> transitions = new LinkedList<T>();
		for (State<T> state : arr)
			if (state.type == StateType.MATCH)
				transitions.add(state.match);
		return transitions;
	}
	
	/** Returns list of available transitions.
	 * @return list of available trantions
	 */
	//@ ensures \return != null;
	public HashSet<T> availableTransitionsUnique() {
		HashSet<T> transitions = new HashSet<T>( arr.size());
		for (State<T> state : arr)
			if (state.type == StateType.MATCH)
				transitions.add(state.match);
		return transitions;
	}
}
