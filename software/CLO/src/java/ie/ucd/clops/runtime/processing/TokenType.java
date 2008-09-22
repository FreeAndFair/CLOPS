
/**
 * Enumeration of token types.
 * <dl>
 * 	<dt>STRING</dt><dd>arbitrary string, parameter on the command line</dd>
 * 	<dt>LEFT</dt><dd>left parenthesis (</dd>
 * 	<dt>RIGHT</dt><dd>right parenthesis )</dd>
 * 	<dt>OR</dt><dd>alternative oprator |</dd>
 * 	<dt>PLUS</dt><dd>plus operator +; one or many times</dd>
 * 	<dt>STAR</dt><dd>star operator *; zero or several times</dd>
 * 	<dt>QUESTION</dt><dd>question mark operator; zero or one time</dd>
 * </dl>
 */
enum TokenType {
	STRING, LEFT, RIGHT, OR, PLUS, STAR, QUESTION
}
