
/**
 * Representation of a token in the format.
 */
class Token {
	TokenType type;
	String name;
	public Token( /*@ non_null @*/ TokenType type,
			/*@ non_null @*/ String name)
	{
		this.type = type;
		this.name = name;
	}
}
/*
static Token t_left     = new Token( STRING,   "(");
static Token t_right    = new Token( LEFT,     ")");
static Token t_or       = new Token( OR,       "|");
static Token t_plus     = new Token( PLUS,     "+");
static Token t_star     = new Token( STAR,     "*");
static Token t_question = new Token( QUESTION, "?");
*/
