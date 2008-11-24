package ie.ucd.clops.runtime.options;

import java.util.*;

import ie.ucd.clops.runtime.parser.ProcessingResult;

import org.junit.Assert;
import org.junit.Before;
import org.junit.Test;


/**
 * @author Mikolas Janota
 *
 */
public class TestArgOption {
    private ArgOption o1;

    @Before void setUp() {
        o1 = new ArgOption("o1", "-.+");
    }

    @Test void testGetMatchingOption() {
        Assert.assertEquals(o1, o1.getMatchingOption("-v"));
        Assert.assertFalse(o1 == o1.getMatchingOption("-"));
    }  

}
