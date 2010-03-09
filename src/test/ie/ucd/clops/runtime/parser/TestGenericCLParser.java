package ie.ucd.clops.runtime.parser;

import ie.ucd.clops.runtime.automaton.Tokenizer;
import ie.ucd.clops.runtime.options.BooleanOption;
import ie.ucd.clops.runtime.options.OptionStore;
import ie.ucd.clops.runtime.rules.RuleStore;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;
import org.junit.Ignore;

/**
 * A class testing the generic command line parser.
 *
 * @author Mikolas Janota
 */
public class TestGenericCLParser {
  private OptionStore os;
  private RuleStore flyStore;
  private BooleanOption bo1;
  private BooleanOption bo2;
  private GenericCLParser gp;
  
  @Before 
  public void setUp() {
    os = new OptionStore();
    bo1 = new BooleanOption("bo1", "-bo");
    bo2 = new BooleanOption("bo2", "-boo");

    os.addOption(bo1);
    os.addOption(bo2);
    
    flyStore = new RuleStore();

    gp = new GenericCLParser();
  }
  
  @Test
  public void testArg() throws Exception { 
      Assert.assertFalse(gp.parse("bo1", os, flyStore, new String[] {"xxxx"}, "tool").successfulParse());
  }
  
  @Test(expected=Tokenizer.UnknownOptionException.class) 
  public void testParserUnknownOptionException2() throws Exception {
    Assert.assertFalse(gp.parse("xxx", os, flyStore, new String[] {"-boo"}, "tool").successfulParse());
  }
  
  
  @Ignore
  public void testParse() throws Exception {
    Assert.assertFalse(gp.parse("bo1", os, flyStore, new String[] {"-boo"}, "tool").successfulParse()); 
                         // shouldn't parse
    Assert.assertTrue(gp.parse("bo2", os, flyStore, new String[] {"-boo"}, "tool").successfulParse()); // should parse
    Assert.assertTrue(gp.parse("bo2?", os, flyStore, new String[] {"-boo"}, "tool").successfulParse()); // should parse
    Assert.assertTrue(gp.parse("bo2*", os, flyStore, new String[] {"-boo" , "-boo" , "-boo"}, "tool").successfulParse());
                         // should parse

    Assert.assertTrue(gp.parse("bo2* bo1*", os, flyStore, 
                               new String[] {"-boo" , "-boo" , "-boo", 
                                             "-bo", "-bo"}, "tool").successfulParse()); // should parse

    Assert.assertFalse(gp.parse("bo2+ bo1*", os, flyStore, 
                                new String[] {"-bo"}, "tool").successfulParse()); // shouldn't go thru

    Assert.assertTrue(gp.parse("(bo2 | bo1)*", os, flyStore, 
                               new String[] {"-bo", "-boo", "-bo", 
                                             "-bo", "-boo"}, "tool").successfulParse()); // should parse

    Assert.assertTrue(gp.parse("bo2*", os, flyStore, 
                               new String[] {"-boo", "-boo", "-boo"}, "tool").successfulParse()); // should parse
  }

}
