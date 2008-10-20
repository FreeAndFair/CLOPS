
package ie.ucd.clops.runtime.automaton;

import ie.ucd.clops.runtime.options.IMatchString;
import ie.ucd.clops.runtime.options.IMatchable;

import java.util.*;

/**
 * Transforming format line into a list of tokens.
 *
 * @author Viliam Holub
 * @author Mikolas Janota
 */
public class Tokenizer {

  static final Token<IMatchable> LEFT     = new Token<IMatchable>( TokenType.LEFT);
  static final Token<IMatchable> RIGHT    = new Token<IMatchable>( TokenType.RIGHT);
  static final Token<IMatchable> OR       = new Token<IMatchable>( TokenType.OR);
  static final Token<IMatchable> PLUS     = new Token<IMatchable>( TokenType.PLUS);
  static final Token<IMatchable> STAR     = new Token<IMatchable>( TokenType.STAR);
  static final Token<IMatchable> QUESTION = new Token<IMatchable>( TokenType.QUESTION);

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

   /** Skips whitespaces in a string from given position.
    * @param text text to process
    * @param index beginning position in text
    * @return new position in the text
    */
   private int skipWhiteSpaces( String text, int index) {
      int text_len = text.length();
      while (index < text_len && Character.isWhitespace( text.charAt(index))) {
         index++;
      }
      return index;
   }

 
   /**
    * Determines whether a given char may belong into an identifier.
    */
   protected boolean isIDChar(char c) {
      return Character.isLetterOrDigit(c) || c == '_' || c == '-';
   }



   /**
    * Split a given string into a list of tokens.
    */
   public List<Token<IMatchable>> tokenize( String format, IMatchString match_this)
      throws IllegalCharacterException, UnknownOptionException {
      LinkedList<Token<IMatchable>> tokens = new LinkedList<Token<IMatchable>>();
      int format_len = format.length();
      int index = skipWhiteSpaces( format, 0);
      
      while (index < format_len) {
         switch (format.charAt( index)) {
         case '(': tokens.add( Tokenizer.LEFT); break;
         case ')': tokens.add( Tokenizer.RIGHT); break;
         case '|': tokens.add( Tokenizer.OR); break;
         case '+': tokens.add( Tokenizer.PLUS); break;
         case '*': tokens.add( Tokenizer.STAR); break;
         case '?': tokens.add( Tokenizer.QUESTION); break;
         default:
            // The first character must be letter or number
            if (!isIDChar( format.charAt(index)))
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
            tokens.add( new Token<IMatchable>( TokenType.MATCH, match));
            break;
         }
         index++;
         index = skipWhiteSpaces( format, index);
      }
      return tokens;
   }
}
