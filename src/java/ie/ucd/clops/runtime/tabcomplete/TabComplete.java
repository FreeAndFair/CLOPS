package ie.ucd.clops.runtime.tabcomplete;

import java.util.*;

import dk.brics.automaton.Automaton;
import dk.brics.automaton.RegExp;
import dk.brics.automaton.State;
import dk.brics.automaton.Transition;


/** Tab completion.
 * 
 * @author Viliam Holub
 *
 */
public class TabComplete {

	
	/** Search result. Used as a return value from graph-searching functions.
	 */
	enum SearchStat {
		/** No word has been added and we have not explored the whole automaton. */
		NONE,
		/** A new word has been added. */
		ADDED,
		/** A new word has been added and we have reach the limit of words. */
		LIMIT,
		/** No word has been added, we explored the whole automaton. */
		END
	};
	
	
	/** Collects words from the given state. Searched down to the specified depth.
	 * 
	 * @param state		state from to follow
	 * @param words		output set of words
	 * @param path		current path in the automaton
	 * @param depth		maximal depth of exploration
	 * @param limit		maximal number of words we are looking for
	 * @return status of the search
	 */
	static SearchStat getWords( State state, Set<String> words,
			StringBuilder path, int depth, int limit) {
		// If we are at the end
		if (depth-- == 0) {
			// Add current path if it is an accepting state
			if (state.isAccept()) {
				words.add( path.toString());
				
				// Return if the list is full
				if (words.size() == limit)
					return SearchStat.LIMIT;
				return SearchStat.ADDED;
			}
			// Return, length is zero
			return SearchStat.NONE;
		}
		
		SearchStat status = SearchStat.END;

		// For each transition from the state
		for (Transition t:state.getTransitions()) {
			// For each character on the transition
			for (int n = t.getMin(); n <= t.getMax(); n++) {
				// Add character to the path
				path.append( (char)n);
				
				// Add strings from followers
				SearchStat result = getWords( t.getDest(), words, path, depth, limit);
				
				// Process result
				switch (result) {
				case NONE: // Nothing happens
					status = SearchStat.NONE;
					break;
				case ADDED: // A word has been added
					status = SearchStat.ADDED;
					break;
				case LIMIT: // List is full
					return SearchStat.LIMIT;
				case END: // Reached the end
					break; 
				}
				
				// Get back character from the path
				path.setLength( path.length()-1); 
			}
		}
		
		// Return, list is not full
		return status;
	}
	
	
	/** Follow the prefix specified in an automaton.
	 * 
	 * @param automaton		automaton to explore
	 * @param prefix		input string to follow
	 * @return set of active states until the last character of the prefix
	 */
	public static Set<State> follow( Automaton automaton, String prefix) {
		// Convert singleton to normal automaton
		automaton.expandSingleton();

		ArrayList<State> dest = new ArrayList<State>();
		IdentityHashMap<State,Integer> wave = new IdentityHashMap<State,Integer>();
		IdentityHashMap<State,Integer> wave_next = new IdentityHashMap<State,Integer>();

		// Kick the first wave with initial state
		wave.put( automaton.getInitialState(), null);

		// For each character in the input string
		for (char c:prefix.toCharArray()) {
			// For each state in a wave
			for (State s:wave.keySet()) {
				// Get states in the next step
				s.step( c, dest);
				
				// Add all next states into the next wave
				for (State q:dest)
					wave_next.put( q, null);
				
				// Clear buffer
				dest.clear();
			}

			// Next wave becomes current wave
			IdentityHashMap<State,Integer> w = wave;
			wave = wave_next;
			wave_next = w;
			wave_next.clear();
		}

		return wave.keySet();
	}


	
	/** Generates a list of alternative completed words.
	 *  
	 * @param regexp	regular expression pattern
	 * @param prefix	prefix of the word
	 * @param limit		maximal number of results returned
	 * @return list of completed words
	 */
	static public List<String> complete( final String regexp, final String prefix, int limit) {
		// Create automaton
		Automaton automaton = new RegExp( regexp).toAutomaton();
		// Find initial states corresponding to the prefix specified
		Set<State> initial_states = follow( automaton, prefix);
		
		StringBuilder buf = new StringBuilder();
		List<String> strings = new ArrayList<String>();
		Set<String> steps = new HashSet<String>();
		
		// Depth of exploring
		int depth = 0;
		// Just in case we have explored the whole automaton
		boolean stop = false;
		
		do {
			stop = true;
			
			// Get words from each state
			for (State state:initial_states)
				if (getWords( state, steps, buf, depth, limit) != SearchStat.END)
					stop = false;
			
			// Prepend found words with prefix and add them to the list
			for (String str:steps)
				strings.add( prefix +str);
			
			// If we had enough words, return
			if (strings.size() >= limit)
				return strings.subList( 0, limit);
			
			// Reset buffers
			buf.setLength( 0);
			steps.clear();
			
			// Increase depth
			depth++;
		} while (!stop);
		
		return strings;
	}
}
