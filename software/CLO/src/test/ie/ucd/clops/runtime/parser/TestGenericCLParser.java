package ie.ucd.clops.runtime.parser;

import ie.ucd.clops.runtime.automaton.Automaton;
import ie.ucd.clops.runtime.automaton.AutomatonException;
import ie.ucd.clops.runtime.automaton.Token;
import ie.ucd.clops.runtime.automaton.Tokenizer;
import ie.ucd.clops.runtime.options.BooleanOption;
import ie.ucd.clops.runtime.options.IMatchable;
import ie.ucd.clops.runtime.options.Option;
import ie.ucd.clops.runtime.options.OptionStore;

import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Set;


import org.junit.*;

/**
 * A class testing the generic command line parser.
 *
 * @author Mikolas Janota
 */
public class TestGenericCLParser {
    private OptionStore os;
    private BooleanOption bo1;
    private BooleanOption bo2;
    private GenericCLParser gp;


    private static Set<String> singleton(String s) {
        Set<String> retv = new HashSet<String>(1);
        retv.add(s);
        return retv;
    }

    @Before public void setUp() {
        os = new OptionStore();
        bo1 = new BooleanOption("bo1", singleton("-bo"));
        bo2 = new BooleanOption("bo2", singleton("-boo"));

        os.addOption(bo1);
        os.addOption(bo2);

        gp = new GenericCLParser();
        System.out.println("TestGenericCLParser was initialized");
    }

    @Test(expected=Tokenizer.UnknownOptionException.class) public void testParserUnknownOptionException1() {
         Assert.assertFalse(gp.parse("bo1", os, new String[] {"xxxx"}));
    }

    @Test(expected=Tokenizer.UnknownOptionException.class) public void testParserUnknownOptionException2() {
        Assert.assertFalse(gp.parse("xxx", os, new String[] {"-boo"}));
    }


    @Test public void testParse() {
        Assert.assertFalse(gp.parse("bo1", os, new String[] {"-boo"})); // shouldn't parse
        Assert.assertTrue(gp.parse("bo2", os, new String[] {"-boo"})); // should parse
        Assert.assertTrue(gp.parse("bo2?", os, new String[] {"-boo"})); // should parse
        Assert.assertTrue(gp.parse("bo2*", os, new String[] {"-boo" , "-boo" , "-boo"})); // should parse

        Assert.assertTrue(gp.parse("bo2* bo1*", os, new String[] {"-boo" , "-boo" , "-boo", "-bo", "-bo"})); // should parse

        Assert.assertFalse(gp.parse("bo2+ bo1*", os, new String[] {"-bo"})); // shouldn't go thru

        Assert.assertTrue(gp.parse("(bo2 | bo1)*", os, new String[] {"-bo", "-boo", "-bo", "-bo", "-boo"})); // should parse

        Assert.assertTrue(gp.parse("bo2*", os, new String[] {"-boo", "-boo", "-boo"})); // should parse
    }

}