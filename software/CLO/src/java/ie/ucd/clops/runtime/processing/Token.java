
package ie.ucd.clops.runtime.processing;

import ie.ucd.clops.runtime.options.*;

/**
 * Representation of a token in the format.
 */
class Token {
	TokenType type;
	IMatchable match;

	public Token( TokenType type) {
		this.type = type;
	}

	public Token( /*@ non_null @*/ TokenType type,
			/*@ non_null @*/ IMatchable match)
	{
		this.type = type;
		this.match = match;
	}

	static final Token LEFT     = new Token( TokenType.LEFT);
	static final Token RIGHT    = new Token( TokenType.RIGHT);
	static final Token OR       = new Token( TokenType.OR);
	static final Token PLUS     = new Token( TokenType.PLUS);
	static final Token STAR     = new Token( TokenType.STAR);
	static final Token QUESTION = new Token( TokenType.QUESTION);
}
