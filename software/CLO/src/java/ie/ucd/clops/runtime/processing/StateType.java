
/**
 * State type.
 * <dl>
 * 	<dt>MATCH</dt><dd>Match with specific option.</dd>
 * 	<dt>SPLIT</dt><dd>Internal state, used for unlabelled transitions.</dd>
 * 	<dt>END</dt><dd>Final, accepting state.</dd>
 * </dl>
 */
enum StateType {
	MATCH, SPLIT, END;
}
