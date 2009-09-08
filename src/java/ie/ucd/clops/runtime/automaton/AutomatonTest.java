
package ie.ucd.clops.runtime.automaton;

/*
 * The implementation slighty follows the reg-exp NDA implementation at
 * http://swtch.com/~rsc/regexp/
 */

import ie.ucd.clops.runtime.automaton.exception.EmptyAlternativeException;
import ie.ucd.clops.runtime.automaton.exception.EmptyFormatException;
import ie.ucd.clops.runtime.automaton.exception.LeftOpenBracketException;
import ie.ucd.clops.runtime.automaton.exception.OpenPlusException;
import ie.ucd.clops.runtime.automaton.exception.OpenQuestionException;
import ie.ucd.clops.runtime.automaton.exception.OpenStarException;
import ie.ucd.clops.runtime.automaton.exception.RightOpenBracketException;
import ie.ucd.clops.runtime.options.BooleanOption;
import ie.ucd.clops.runtime.options.IMatchable;
import ie.ucd.clops.runtime.options.Option;
import ie.ucd.clops.runtime.options.OptionStore;

import java.util.Collection;
import java.util.List;
import java.util.Arrays;



/**
 * Represents format of the command line as an automaton and allows traversing
 * the automaton with options.
 *
 * @author Viliam Holub
 */
public class AutomatonTest {

	private static int test_no;
	private static int test_no_ok;
	private static int test_no_fail;

	private static String stringTransitions( Collection<IMatchable> c) {
		String result = "";
		String[] results = new String[ c.size()];
		int i=0;
		for (IMatchable m:c)
			results[ i++] = m.getIdentifier();
		Arrays.sort( results);
		for (String s:results)
			result += s+" ";
			
		return result;
	}

	private static String stringTokens( List<Token<IMatchable>> tokens) {
		StringBuilder result = new StringBuilder();
		//boolean last_match = false;
		for (Token<IMatchable> token:tokens) {
			switch (token.type) {
			case MATCH: result.append("'" +token.match.getIdentifier() +"' "); break;
			case LEFT: result.append('('); break;
			case RIGHT: result.append(')'); break;
			case OR: result.append('|'); break;
			case PLUS: result.append('+'); break;
			case STAR: result.append('*'); break;
			case QUESTION: result.append('?'); break;
			}
		}
		return result.toString();
	}

	//	public static String stringOptions( Option[] options) {
	//		String result = "";
	//		for (Option o:options)
	//			result += o.getAliases().iterator().next() +" ";
	//		return result;
	//	}

	private static String stage;

	private static class TestInstance {
		String stage;
		String format;
		Option<?>[] follow;
		String result;
		TestInstance( String stage, String format, Option<?>[] follow, String result) {
			this.stage = stage;
			this.format = format;
			this.follow = follow;
			this.result = result;
		}

	}

	private static void newStage( String new_stage) {
		if (new_stage == null || new_stage.equals("") || new_stage.equals( stage))
			return;
		stage = new_stage;
		test_no = 0;
	}

	private static void automaton_test(
			OptionStore os,
			TestInstance ti) {
		List<Token<IMatchable>> tokens = null;
		Automaton<IMatchable>.AutomatonRun r = null;
		Automaton<IMatchable> a = null;
		String result = "";

		newStage( ti.stage);
		test_no++;

		try {
			tokens = new Tokenizer().tokenize( ti.format, os);
			a = new Automaton<IMatchable>( tokens);
			r = a.run();
			for (Option<?> o:ti.follow)
				r.nextStep( o);
			result = stringTransitions( r.availableTransitions());
			if (r.isAccepting())
				result += "accepting";
			if (r.inErrorState())
				result += "error";
		}
		catch (Tokenizer.IllegalCharacterException e) {result = "Tokenizer.IllegalCharacterException";}
		catch (Tokenizer.UnknownOptionException e) {result = "Tokenizer.UnknownOptionException";}
		catch (RightOpenBracketException e) {result = "RightOpenBracketException";}
		catch (LeftOpenBracketException e) {result = "LeftOpenBracketException";}
		catch (OpenQuestionException e) {result = "OpenQuestionException";}
		catch (OpenStarException e) {result = "OpenStarException";}
		catch (OpenPlusException e) {result = "OpenPlusException";}
		catch (EmptyAlternativeException e) {result = "EmptyAlternativeException";}
		catch (EmptyFormatException e) {result = "EmptyFormatException";}
		catch (Exception e) {result = "Unhandled exception";}

		if (result.equals( ti.result)) {
			// Comment this out to get "cleaner" test results
			//System.out.print( "Stage " +stage +"/" +test_no +": ");
			//System.out.println( "[	OK	]");
			test_no_ok++;
		} else {
			System.out.print( "Stage " +stage +"/" +test_no +": ");
			System.out.println( "[ FAIL ] expected '" +ti.result +"' get '"
					+result +"'");
			System.out.println( "\tFormat: " +ti.format);
			System.out.println( "\tTokens: " +stringTokens( tokens));
			//System.out.println( "\tFollow: " +stringOptions( ti.follow));
			test_no_fail++;
		}
	}

	public static void main(String[] args) throws Exception {

		OptionStore os = new OptionStore();
		Option<?> bo1 = new BooleanOption("bo1", "bo1");
		Option<?> bo2 = new BooleanOption("bo2", "bo2");
		Option<?> bo3 = new BooleanOption("bo3", "bo3");
		Option<?> bo4 = new BooleanOption("bo4", "bo4");

		os.addOption( bo1);
		os.addOption( bo2);
		os.addOption( bo3);
		os.addOption( bo4);

		TestInstance[] test_instances = new TestInstance[] {
			new TestInstance( "Empty(1)      ", "", new Option[] {}, "EmptyFormatException"),
			new TestInstance( "Follow(1)     ", "bo1 bo2 bo3", new Option[] {}, "bo1 "),
			new TestInstance( "",               "bo1 bo2 bo3", new Option[] {bo1}, "bo2 "),
			new TestInstance( "",               "bo1 bo2 bo3", new Option[] {bo1, bo2}, "bo3 "),
			new TestInstance( "",               "bo1 bo2 bo3", new Option[] {bo1, bo2, bo3}, "accepting"),
			new TestInstance( "",               "(bo1 bo2) bo3", new Option[] {}, "bo1 "),
			new TestInstance( "",               "bo1 (bo2 bo3)", new Option[] {}, "bo1 "),

			new TestInstance( "Alternative(1)", "bo1|bo2", new Option[] {}, "bo1 bo2 "),
			new TestInstance( "",               "bo1|bo2", new Option[] {bo1}, "accepting"),
			new TestInstance( "",               "bo1|bo2", new Option[] {bo2}, "accepting"),
			new TestInstance( "",               "bo1|bo2", new Option[] {bo3}, "error"),

			new TestInstance( "Alternative(2)", "bo1|bo2 bo3", new Option[] {}, "bo1 bo2 "),
			new TestInstance( "",               "bo1|bo2 bo3", new Option[] {bo1}, "accepting"),
			new TestInstance( "",               "bo1|bo2 bo3", new Option[] {bo2}, "bo3 "),
			new TestInstance( "",               "bo1|bo2 bo3", new Option[] {bo1, bo3}, "error"),
			new TestInstance( "",               "bo1|bo2 bo3", new Option[] {bo2, bo3}, "accepting"),
			new TestInstance( "",               "bo1|bo2 bo3", new Option[] {bo1, bo3, bo1}, "error"),

			new TestInstance( "Alternative(3)", "bo1|bo2|bo3", new Option[] {}, "bo1 bo2 bo3 "),
			new TestInstance( "",               "bo1|bo2|bo3", new Option[] {bo1}, "accepting"),
			new TestInstance( "",               "bo1|bo2|bo3", new Option[] {bo2}, "accepting"),
			new TestInstance( "",               "bo1|bo2|bo3", new Option[] {bo3}, "accepting"),
			new TestInstance( "",               "bo1|bo2|bo3", new Option[] {bo2, bo3}, "error"),

			new TestInstance( "Alternative(4)", "|bo1",   new Option[] {}, "EmptyAlternativeException"),
			new TestInstance( "",               "bo1|",   new Option[] {}, "EmptyAlternativeException"),
			new TestInstance( "",               "(bo1|)", new Option[] {}, "RightOpenBracketException"),
			new TestInstance( "",               "(|bo1)", new Option[] {}, "EmptyAlternativeException"),

			new TestInstance( "Alternative(5)", "bo1||bo2", new Option[] {}, "bo1 bo2 "),

			new TestInstance( "Question(1)   ", "bo1?", new Option[] {}, "bo1 accepting"),
			new TestInstance( "",               "?", new Option[] {}, "OpenQuestionException"),
			new TestInstance( "",               "bo1?bo2", new Option[] {}, "bo1 bo2 "),
			new TestInstance( "",               "bo1?bo2", new Option[] {bo1}, "bo2 "),
			new TestInstance( "",               "bo1?bo2", new Option[] {bo2}, "accepting"),
			new TestInstance( "Question(2)   ", "bo1?", new Option[] {}, "bo1 accepting"),
			new TestInstance( "",               "bo1?|bo2", new Option[] {}, "bo1 bo2 accepting"),
			new TestInstance( "",               "bo1?|bo2", new Option[] {bo1}, "accepting"),
			new TestInstance( "",               "bo1?|bo2", new Option[] {bo2}, "accepting"),

			new TestInstance( "Star(1)       ", "bo1*", new Option[] {}, "bo1 accepting"),
			new TestInstance( "",               "bo1*", new Option[] {bo1}, "bo1 accepting"),
			new TestInstance( "",               "bo1*", new Option[] {bo1, bo1}, "bo1 accepting"),
			new TestInstance( "Star(2)       ", "*", new Option[] {}, "OpenStarException"),
			new TestInstance( "",               "(* bo1)", new Option[] {bo1, bo1}, "OpenStarException"),
			new TestInstance( "",               "(bo1|*)", new Option[] {bo1, bo1}, "OpenStarException"),
			new TestInstance( "Star(3)       ", "(bo1|bo2)*", new Option[] {}, "bo1 bo2 accepting"),
			new TestInstance( "",               "(bo1|bo2)* bo3", new Option[] {bo1}, "bo1 bo2 bo3 "),
			new TestInstance( "",               "(bo1|bo2)* bo3", new Option[] {bo2}, "bo1 bo2 bo3 "),
			new TestInstance( "",               "(bo1|bo2)* bo3", new Option[] {bo3}, "accepting"),
			new TestInstance( "",               "(bo1|bo2)* bo3", new Option[] {bo1, bo2, bo3}, "accepting"),
			new TestInstance( "Star(4)",        "bo1* bo1", new Option[] {bo1, bo1}, "bo1 bo1 accepting"),

			new TestInstance( "Plus(1)       ", "bo1+", new Option[] {}, "bo1 "),
			new TestInstance( "",               "bo1+", new Option[] {bo1}, "bo1 accepting"),
			new TestInstance( "",               "bo1+", new Option[] {bo1, bo1}, "bo1 accepting"),
			new TestInstance( "Plus(2)       ", "+", new Option[] {}, "OpenPlusException"),
			new TestInstance( "",               "(+ bo1)", new Option[] {bo1, bo1}, "OpenPlusException"),
			new TestInstance( "",               "(bo1|+)", new Option[] {bo1, bo1}, "OpenPlusException"),
			new TestInstance( "Plus(3)       ", "(bo1|bo2)+", new Option[] {}, "bo1 bo2 "),
			new TestInstance( "",               "(bo1|bo2)+ bo3", new Option[] {bo1}, "bo1 bo2 bo3 "),
			new TestInstance( "",               "(bo1|bo2)+ bo3", new Option[] {bo2}, "bo1 bo2 bo3 "),
			new TestInstance( "",               "(bo1|bo2)+ bo3", new Option[] {bo3}, "error"),
			new TestInstance( "",               "(bo1|bo2)+ bo3", new Option[] {bo1, bo2, bo3}, "accepting"),

			new TestInstance( "Complex(1)    ", "(bo1 bo2|bo3)+ bo2* bo3?", new Option[] {}, "bo1 bo3 "),
			new TestInstance( "",               "(bo1 bo2|bo3)+ bo2* bo3?", new Option[] {bo1}, "bo2 "),
			new TestInstance( "",               "(bo1 bo2|bo3)+ bo2* bo3?", new Option[] {bo2}, "error"),
			new TestInstance( "",               "(bo1 bo2|bo3)+ bo2* bo3?", new Option[] {bo3}, "bo1 bo2 bo3 bo3 accepting"),
			new TestInstance( "",               "(bo1 bo2|bo3)+ bo2* bo3?", new Option[] {bo3,bo2}, "bo2 bo3 accepting"),
			new TestInstance( "",               "(bo1 bo2|bo3)+ bo2* bo3?", new Option[] {bo3,bo2,bo3}, "accepting"),
			new TestInstance( "",               "(bo1 bo2|bo3)+ bo2* bo3?", new Option[] {bo3,bo2,bo2,bo3}, "accepting"),
			new TestInstance( "",               "(bo1 bo2|bo3)+ bo2* bo3?", new Option[] {bo3,bo2,bo2,bo3,bo3}, "error"),

			new TestInstance( "Complex(2)    ", "(bo1*|bo2*)*", new Option[] {bo1,bo2,bo1,bo1}, "bo1 bo2 accepting"),
			new TestInstance( "",               "(bo1*|bo2*)* bo3", new Option[] {bo1,bo2,bo1,bo1}, "bo1 bo2 bo3 "),
		};

		for (TestInstance ti : test_instances)
			automaton_test( os, ti);

		System.out.println( "" +test_no_ok +" test(s) OK, " +test_no_fail +" test(s) fails");
	}
}
