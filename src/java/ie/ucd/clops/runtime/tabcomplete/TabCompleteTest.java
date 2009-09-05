package ie.ucd.clops.runtime.tabcomplete;

import static org.junit.Assert.*;

import java.util.List;

import org.junit.Test;


/** Test tab completion.
 * 
 * @author Viliam Holub
 * 
 */
public class TabCompleteTest {
	

	/** Test tab completion.
	 * 
	 */
	@Test
	public void completeTest() {
		
		// Basic completion tests
		completeSubTest( "abc", "",		20, "abc -");
		completeSubTest( "abc", "a",	20, "abc -");
		completeSubTest( "abc", "ab",	20, "abc -");
		completeSubTest( "abc", "abc",	20, "abc -");
		
		// Fail in prefix match
		completeSubTest( "abc", "x",	20, "-");
		completeSubTest( "abc", "abcd",	20, "-");
		
		// Standard test 1
		completeSubTest( "(a|b|c|d|e)b*z", "", 0, "-");
		completeSubTest( "(a|b|c|d|e)b*z", "", 1, "az -");
		completeSubTest( "(a|b|c|d|e)b*z", "", 2, "az bz -");
		completeSubTest( "(a|b|c|d|e)b*z", "", 3, "az bz cz -");
		completeSubTest( "(a|b|c|d|e)b*z", "", 4, "az bz dz cz -");
		completeSubTest( "(a|b|c|d|e)b*z", "", 10, "az bz dz ez cz bbz abz dbz ebz cbz -");
		
		// Standard test 2
		completeSubTest( "(a|b|c|d|e)b*z", "ab", 0, "-");
		completeSubTest( "(a|b|c|d|e)b*z", "ab", 1, "abz -");
		completeSubTest( "(a|b|c|d|e)b*z", "ab", 2, "abz abbz -");
		completeSubTest( "(a|b|c|d|e)b*z", "ab", 3, "abz abbz abbbz -");
		completeSubTest( "(a|b|c|d|e)b*z", "ab", 4, "abz abbz abbbz abbbbz -");
		completeSubTest( "(a|b|c|d|e)b*z", "ab", 5, "abz abbz abbbz abbbbz abbbbbz -");
		
		// Corner tests
		completeSubTest( "*abc", "",	20, "*abc -");
		completeSubTest( "abc\\", "",	20, "IllegalArgumentException");
		completeSubTest( "a[bc", "",	20, "IllegalArgumentException");
		completeSubTest( "a{bc", "",	20, "IllegalArgumentException");
		completeSubTest( "a(bc", "",	20, "IllegalArgumentException");
	}
	
	
	
	/*
	 * 
	 * Private
	 * 
	 */

	
	/** Generates a simple text from the list of strings.
	 * 
	 * @param strings list of strings
	 * @return one compact string
	 */
	private static String collect( final List<String> strings) {
		String all = "";
		for (String s:strings)
			all += s +" ";
		return all +"-";
	}
	
	
	/** One particular test of tab completion.
	 * 
	 * @param regexp	regular expression
	 * @param prefix	prefix to complete
	 * @param limit		maximal number of results
	 * @param expected	expected output in a compact form
	 */
	private void completeSubTest( final String regexp, final String prefix,
			final int limit, final String expected) {

		List<String> strings;
		String result;
		try {
			strings = TabComplete.complete( regexp, prefix, limit);
			result = collect( strings);
		}
		catch (IllegalArgumentException e) {
			result = "IllegalArgumentException";
		}
		 
		assertTrue( "Expecting \""+ expected +"\" but got \"" +result +"\" for "+regexp +" with prefix "+prefix,
				result.equals( expected));
	}
}
