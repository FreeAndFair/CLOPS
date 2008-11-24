package ie.ucd.clops.runtime.options;

import org.junit.Before;
import org.junit.Test;


/**
 * @author Mikolas Janota
 *
 */
public class TestArgOption {
    private ArgOption o1;

    @Before public void setUp() {
        o1 = new ArgOption("o1", "-.+");
    }

    @Test public void testGetMatchingOption() {
        //Assert.assertEquals(o1, o1.getMatchingOption("-v"));
        //Assert.assertFalse(o1 == o1.getMatchingOption("-"));
    }  

}
