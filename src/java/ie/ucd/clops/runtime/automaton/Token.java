
package ie.ucd.clops.runtime.automaton;


/**
 * Representation of a token in the regular expression (command line format).
 * @author Viliam Holub
 * @param <T> the type of the entity that has generated this token
 */
public class Token<T> {
	public TokenType type;
	public T match;

	public Token( TokenType type) {
            this.type = type;
	}

	public Token(/*@ non_null @*/ TokenType type,
		     /*@ non_null @*/ T match) {
            this.type = type;
            this.match = match;
	}
}
