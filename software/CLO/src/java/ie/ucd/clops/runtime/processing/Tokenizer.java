
package ie.ucd.clops.runtime.processing;

import java.util.*;
import java.lang.*;

import ie.ucd.clops.runtime.options.*;

/**
 * Transforming format line into a list of tokens.
 */
class Tokenizer {


	public class TokenizerException extends Exception {
		private static final long serialVersionUID = 1L;
	}

	public class IllegalCharacterException extends TokenizerException {
		private static final long serialVersionUID = 1L;
		public int index;
		IllegalCharacterException( int index) {
			this.index = index;
		}
	}

	public class UnknownOptionException extends TokenizerException {
		private static final long serialVersionUID = 1L;
		public String opt_name;
		UnknownOptionException( String opt_name) {
			this.opt_name = opt_name;
		}
	}

	/** Skips whitespaces in the strinh from given position.
	 * @param text text to process
	 * @param index beginning position in text
	 * @return new position in the text
	 */
	int skipWhiteSpaces( String text, int index) {
		int text_len = text.length();
		while (index < text_len && Character.isWhitespace( text.charAt(index)))
			index++;
		return index;
	}

	public class MatchThis {
		IMatchable getMatchable( String param) {
			return null;
		}
	}

	Collection<Token> tokenize( String format, MatchThis match_this)
		throws IllegalCharacterException, UnknownOptionException {
		ArrayList<Token> tokens = new ArrayList<Token>();
		int format_len = format.length();
		int index = skipWhiteSpaces( format, 0);

		while (index < format_len) {
			switch (format.charAt( 0)) {
				case '(': tokens.add( Token.LEFT); break;
				case ')': tokens.add( Token.RIGHT); break;
				case '|': tokens.add( Token.OR); break;
				case '+': tokens.add( Token.PLUS); break;
				case '*': tokens.add( Token.STAR); break;
				case '?': tokens.add( Token.QUESTION); break;
				default:
					// The first character must be letter or number
					if (!Character.isLetterOrDigit( format.charAt(index)))
						throw new IllegalCharacterException( index);
					
					// Get the parameter
					int i = index+1;
					while (i < format_len && Character.isLetterOrDigit( format.charAt( i)))
						i++;
					String param = format.substring( index, i);
					index = i-1;
					// Convert parameter to option or option group
					IMatchable match = match_this.getMatchable( param);
					if (match == null)
						throw new UnknownOptionException( param);
					tokens.add( new Token( TokenType.MATCH, match));
					break;
			}
			index++;
			index = skipWhiteSpaces( format, index);
		}
		return tokens;
	}
}
