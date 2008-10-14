
package ie.ucd.clops.runtime.processing;

/*
 * The implementation slighty follows the reg-exp NDA implementation at
 * http://swtch.com/~rsc/regexp/
 */

import ie.ucd.clops.runtime.options.*;

import java.util.ArrayList;
import java.util.Stack;


/**
 * Represents format of the command line as an automaton and allows travesing
 * the automaton with options.
 *
 * @author Viliam Holub
 */
class Automaton {

	/** Step serial number.
	 * Step number is used for effective creation of the list of active
	 * states. */
	int step_index;
	/** Indication of error state.
	 * If this variable is set, we are in the error state. */
	boolean error;
	/** Starting state of the automaton. */
	State /*@ non_null @*/ start_state;
	/** List of active states.
	 * The list is updated every step. */
	ArrayList<State> /*@ non_null @*/ arr;
	/** Backup of active states.
	 * The backup is used for error reporting only. */
	ArrayList<State> /*@ non_null @*/ arr_backup;

	/** Creates automaton representation of command line format.
	 */
	//@ tokens.size() != 0;
	Automaton( /*@ non_null @*/ Token[] tokens) {
		arr = arr_backup = new ArrayList<State>();
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
	private void build( /*@ non_null @*/ Token[] tokens) {
		// Stack of contexts, each context represents nested ()
		Stack<Context> ctxs = new Stack<Context>();
		// Fragments of automaton
		Stack<Fragment> fragments = new Stack<Fragment>();
		// Current context
		Context ctx = new Context();

		for (Token t:tokens) switch (t.type) {
			case MATCH:
				// If there are two atom fragments on stack, concatenate
				if (ctx.atoms > 1) {
					Fragment f = fragments.pop();
					fragments.peek().concatenate( f);
					ctx.atoms--;
				}
				// Create fragment that matches the given string
				// Push fragment into stack
				fragments.push( new Fragment( new State( StateType.MATCH, t.match)));
				ctx.atoms++;
				break;
			case LEFT:
				// Concatenate atoms on stack
				if (ctx.atoms > 1) {
					Fragment f = fragments.pop();
					fragments.peek().concatenate( f);
					ctx.atoms--;
				}
				// Save context and create a new one
				ctxs.push( ctx);
				ctx = new Context();
				break;
			case RIGHT:
				// Test if right brace without left one
				if (ctxs.size() == 0) {
					//TODO: raise syntax error
				}
				// If there are no atoms, syntax error -- ok if alternatives != 0
				if (ctx.atoms == 0) {
					// TODO: raise syntax error
				}
				// Concatenate atoms on stack
				if (ctx.atoms > 1) {
					Fragment f = fragments.pop();
					fragments.peek().concatenate( f);
					ctx.atoms--;
				}
				// Create alternatives from fragments on stack
				if (ctx.alternatives > 0) {
					fragments.push( Fragment.alternative(
						fragments.pop(), fragments.pop()));
				}
				// Recover old context
				ctx = ctxs.pop();
				ctx.atoms++;
				break;
			case OR:
				// If there are no fragments, raise error
				// TODO
				// FIXME: this may be absolutely legal
				
				if (ctx.atoms == 0 && ctx.alternatives == 0) {
					// TODO: what now?
				}
				if (ctx.atoms == 0 && ctx.alternatives != 0) {
					// TODO: use of double alternative ||
				}
				
				// Concatenate fragments on stack
				while (ctx.atoms>1) {
					// Concatenate two fragments
					Fragment f = fragments.pop();
					fragments.peek().concatenate( f);
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
			case STAR:
			case QUESTION:
				// If there are no atom fragments, raise error
				if (ctx.atoms == 0) {
					// TODO: raise error
				}

				// Apply operator to the last fragment
				fragments.push( Fragment.apply_operator( t.type, fragments.pop()));
				break;
		}

		// Report error if there are unclosed brackets
		if (ctxs.size() != 0) {
			// TODO
		}
		// If the stack is empty, comply
		if (fragments.size() == 0) {
			// TODO
		}
		// Concatenate any residual atoms
		if (ctx.atoms > 1) {
			Fragment f = fragments.pop();
			fragments.peek().concatenate( f);
		}
		// If there is unclosed alternative, close it
		if (ctx.alternatives != 0) {
			fragments.push( Fragment.alternative(
					fragments.pop(), fragments.pop()));
		}
		// Create final fragment
		State s = new State( StateType.END, null, null, null);
		Fragment fin = fragments.pop();
		fin.assignNext( s);
		
		assert fragments.isEmpty();

		// Write start state
		start_state = new State( StateType.SPLIT, null, fin.start, null);
	}

	/** Adds successors of s which has the type MATCH or END.
	 * To avoid duplicates in the output list (and avoid cycling as well),
	 * we update each state with step index and add only those, which state
	 * index is less than the current one.
	 * @param s state to add or follow
	 * @param ll output list of states
	 */
	private void addSuccessors2( State s,
			/*@ non_null @*/ArrayList<State> ll) {
		if (s == null || s.state_index == step_index)
			return;
		s.state_index = step_index;
		if (s.type == StateType.SPLIT) {
			addSuccessors2( s.next1, ll);
			addSuccessors2( s.next2, ll);
		} else {
			ll.add( s);
		}
	}

	/** Adds successors of s of the type MATCH or END to the list.
	 * Type of the state s must by MATCH or END.
	 * @param s state to follow
	 * @param ll output list of states
	 */
	private void addSuccessors( /*@ non_null @*/ State s,
			/*@ non_null @*/ArrayList<State> ll) {
		if (s.state_index == step_index)
			return;
		addSuccessors2( s.next1, ll);
		addSuccessors2( s.next2, ll);
		s.state_index = step_index;
	}

	/** Tests if the current state matched with the token, follows outgoing
	 * transitions if so and saves successor states.
	 * @param s state to follow
	 * @param t current option to process
	 * @param ll list of successor states
	 */
	private void follow( /*@ non_null @*/ State s,
			/*@ non_null @*/ Option o,
			/*@ non_null @*/ ArrayList<State> ll) {
		// Type of the state must be ready to match.
		if (s.type != StateType.MATCH)
			return;
		// Test the state if matches.
		if (!s.match.doIMatch( o))
			return;
		// We have a match, add succesors
		addSuccessors( s, ll);
	}

	/** Apply next step in automaton.
	 * @param t option to process
	 * @returns if the option is correctly positioned according to format
	 */
	public boolean nextStep( /*@ non_null @*/ Option o) {
		// Do not continue if we are in an error state
		if (error)
			return false;

		// Process next step, store states
		ArrayList<State> arr2 = new ArrayList<State>();
		for (State s:arr)
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

	/** Returns if the current automaton state is accepting.
	 */
	public boolean isAccepting() {
		for (State s:arr) {
			if (s.type == StateType.END)
				return true;
		}
		return false;
	}
	
	/** Returns list of available options.
	 */
	
	public ArrayList<IMatchable> availableOptions() {
		ArrayList<IMatchable> ll = new ArrayList<IMatchable>();
		for (State s:arr)
			ll.addAll( s.match.getOptions());
	}
	


/*
	public static void main( String[] argv) {
		Token[] tokens;
		Option[] options;

		Automaton a;

		// Internal tests
		tokens = new Token[ 8];
		tokens[ 0] = new Token( Token.OPTION, "Ahoj");
		tokens[ 1] = new Token( Token.OPTION, "Options");
		tokens[ 2] = new Token( Token.LEFT);
		tokens[ 3] = new Token( Token.OPTION, "OtherOptions");
		tokens[ 4] = new Token( Token.OR);
		tokens[ 5] = new Token( Token.OPTION, "What");
		tokens[ 6] = new Token( Token.RIGHT);
		tokens[ 7] = new Token( Token.STAR);
		options = new Option[ 5];
		options[ 0] = new Option( "Ahoj");
		options[ 1] = new Option( "Options");
		options[ 2] = new Option( "OtherOptions");
		options[ 3] = new Option( "What");
		options[ 4] = new Option( "OtherOptions");
		a = new Automaton( tokens);
		for (Option o:options) {
			System.out.print( "Step \"" +o.name +"\": ");
			a.nextStep( o);
			System.out.print( " " +(a.error ? "error" : "ok"));
			System.out.print( " " +(a.isAccepting() ? "acceptiong" : ""));
			System.out.println( "");
		}
	}
*/
}
