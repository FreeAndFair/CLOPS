package ie.ucd.clops.runtime.parser;

import ie.ucd.clops.runtime.automaton.Tokenizer;
import ie.ucd.clops.runtime.flyrules.FlyRuleStore;
import ie.ucd.clops.runtime.options.BooleanOption;
import ie.ucd.clops.runtime.options.OptionStore;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;

/**
 * A class testing the generic command line parser.
 *
 * @author Mikolas Janota
 */
public class TestGenericCLParser {
    private OptionStore os;
    private FlyRuleStore flyStore;
    private BooleanOption bo1;
    private BooleanOption bo2;
    private GenericCLParser gp;

    @Before public void setUp() {
        os = new OptionStore();
        bo1 = new BooleanOption("bo1", "-bo");
        bo2 = new BooleanOption("bo2", "-boo");

        os.addOption(bo1);
        os.addOption(bo2);
        
        flyStore = new FlyRuleStore();

        gp = new GenericCLParser();
    }

    @Test public void testArg() 
        throws Tokenizer.UnknownOptionException, Tokenizer.IllegalCharacterException {
        Assert.assertFalse(gp.parse("bo1", os, flyStore, new String[] {"xxxx"}));
    }

    @Test(expected=Tokenizer.UnknownOptionException.class) 
        public void testParserUnknownOptionException2() 
                          throws Tokenizer.UnknownOptionException, Tokenizer.IllegalCharacterException {
        Assert.assertFalse(gp.parse("xxx", os, flyStore, new String[] {"-boo"}));
    }


    @Test public void testParse() throws Tokenizer.UnknownOptionException, Tokenizer.IllegalCharacterException {
        Assert.assertFalse(gp.parse("bo1", os, flyStore, new String[] {"-boo"})); // shouldn't parse
        Assert.assertTrue(gp.parse("bo2", os, flyStore, new String[] {"-boo"})); // should parse
        Assert.assertTrue(gp.parse("bo2?", os, flyStore, new String[] {"-boo"})); // should parse
        Assert.assertTrue(gp.parse("bo2*", os, flyStore, new String[] {"-boo" , "-boo" , "-boo"})); // should parse

        Assert.assertTrue(gp.parse("bo2* bo1*", os, flyStore, new String[] {"-boo" , "-boo" , "-boo", "-bo", "-bo"})); // should parse

        Assert.assertFalse(gp.parse("bo2+ bo1*", os, flyStore, new String[] {"-bo"})); // shouldn't go thru

        Assert.assertTrue(gp.parse("(bo2 | bo1)*", os, flyStore, new String[] {"-bo", "-boo", "-bo", "-bo", "-boo"})); // should parse

        Assert.assertTrue(gp.parse("bo2*", os, flyStore, new String[] {"-boo", "-boo", "-boo"})); // should parse
    }

}
