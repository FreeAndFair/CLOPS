
package ie.ucd.clops.runtime.automaton;

/*
 * The implementation slighty follows the reg-exp NDA implementation at
 * http://swtch.com/~rsc/regexp/
 */

import ie.ucd.clops.runtime.options.OptionStore; //XXX for tests
import ie.ucd.clops.runtime.options.BooleanOption;
import ie.ucd.clops.runtime.options.IMatchable;
import ie.ucd.clops.runtime.options.Option;


import java.util.*;



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
			throws RightOpenBracketException, LeftOpenBracketException, OpenQuestionException {
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
			throws RightOpenBracketException, LeftOpenBracketException, OpenQuestionException {
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
					// TODO: raise syntax error
				}
				// Concatenate atoms on stack
				if (ctx.atoms > 1) {
					Fragment<T> f = fragments.pop();
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
					// Use of multiple alternatives ||
					break;
				}
				
				// Concatenate fragments on stack
				while (ctx.atoms>1) {
					// Concatenate two fragments
					Fragment<T> f = fragments.pop();
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
				if (ctx.atoms == 0)
					throw new OpenQuestionException();

				// Apply operator to the last fragment
				fragments.push( Fragment.apply_operator( t.type, fragments.pop()));
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
	 * @param s state to add or follow
	 * @param ll output list of states
	 */
	private void addSuccessors2( State<T> s,
			/*@ non_null @*/ List<State<T>> ll) {
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
	private void addSuccessors( /*@ non_null @*/ State<T> s,
			/*@ non_null @*/List<State<T>> ll) {
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
	private void follow( /*@ non_null @*/ State<T> s,
			/*@ non_null @*/ T o,
			/*@ non_null @*/ List<State<T>> arr) {
		// Type of the state must be ready to match.
		if (s.type != StateType.MATCH)
			return;
		// Test the state if matches.
		if (!s.match.equals(o)) {
		  return;
		}
		// We have a match, add succesors
		addSuccessors( s, arr);
	}

	/** Apply next step in automaton.
	 * @param o option to process
	 * @return if the option is correctly positioned according to format
	 */
	public boolean nextStep( /*@ non_null @*/ T o) {
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

	/** Returns if the current automaton state is accepting.
	 */
	public boolean isAccepting() {
		for (State<T> s:arr) {
			if (s.type == StateType.END)
				return true;
		}
		return false;
	}
	
	/** Returns list of available options.
	 */
	
	public List<T> availableTransitions() {
		List<T> transitions = new LinkedList<T>();
		for (State<T> state : arr)
			if (state.type == StateType.MATCH)
				transitions.add(state.match);
		return transitions;
	}
	
	
	
	/*==== Testing ====*/
   private static Set<String> singleton(String s) {
      Set<String> retv = new HashSet<String>(1);
      retv.add(s);
      return retv;
   }

   	private static void automaton_test( String format, OptionStore os) {
		try {
			Automaton<IMatchable> a = new Automaton<IMatchable>( new Tokenizer().tokenize( format, os));
		}
		catch (ie.ucd.clops.runtime.automaton.Tokenizer.IllegalCharacterException e) {
			
		}
		catch (ie.ucd.clops.runtime.automaton.RightOpenBracketException e) {

		}
		catch (ie.ucd.clops.runtime.automaton.LeftOpenBracketException e) {
		}
		catch (ie.ucd.clops.runtime.automaton.OpenQuestionException e) {
		}
		catch (Tokenizer.TokenizerException e) {
		}
	}
	
	public static void main(String[] args) throws Exception {
		System.out.println( "works");

		String s1 = "bo1 bo2 bo3";

		OptionStore os = new OptionStore();
		Option o1 = new BooleanOption("bo1", singleton("-b1"));
		Option o2 = new BooleanOption("bo2", singleton("-b2"));
		Option o3 = new BooleanOption("bo3", singleton("-b3"));
		Option o4 = new BooleanOption("bo4", singleton("-b4"));

		os.addOption( o1);
		os.addOption( o2);
		os.addOption( o3);
		os.addOption( o4);

		automaton_test( "bo1 bo2 bo3", os);

		/*
		OptionStore os = new OptionStore();
		BooleanOption bo1 = new BooleanOption("bo1", singleton("-bo"));
		BooleanOption bo2 = new BooleanOption("bo2", singleton("-boo"));

		os.addOption(bo1);
		os.addOption(bo2);

		GenericCLParser gp = new GenericCLParser(os.getOptions());
		assert !gp.parse("-bo", os, new String[] {"-boo"}); // shouldn't parse
		assert gp.parse("-boo", os, new String[] {"-boo"}); // should parse
		assert gp.parse("-boo?", os, new String[] {"-boo"}); // should parse
		assert gp.parse("-boo*", os, new String[] {"-boo" , "-boo" , "-boo"}); // should parse

		assert gp.parse("-boo* -bo*", os, new String[] {"-boo" , "-boo" , "-boo", "-bo", "-bo"}); // should parse

		assert !gp.parse("-boo+ -bo*", os, new String[] {"-bo"}); // shouldn't go thru

		assert gp.parse("(-boo | -bo)*", os, new String[] {"-bo", "-boo", "-bo", "-bo", "-boo"}); // should parse

		assert gp.parse("-boo*", os, new String[] {"-boo", "-boo", "-boo"}); // should parse

		assert !gp.parse("-bo", os, new String[] {"xxxx"});

		try {
			gp.parse("xxx", os, new String[] {"-boo"});
			assert false;
		} catch (UnknownOptionException e) {
			assert true;
		}
		*/
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
