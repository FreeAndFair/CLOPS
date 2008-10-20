
package ie.ucd.clops.runtime.automaton;


/**
 * Representation of a token in the format.
 */
public class Token<T> {
	TokenType type;
	T match;

	public Token( TokenType type) {
		this.type = type;
	}

	public Token( /*@ non_null @*/ TokenType type,
			/*@ non_null @*/ T match)
	{
		this.type = type;
		this.match = match;
	}
}