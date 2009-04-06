package ie.ucd.clops.test;

import ie.ucd.clops.dsl.Main;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.List;

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.Lexer;
import org.antlr.runtime.RecognitionException;

public class TestGen {

  private static void runTests(List<TestSet> tests, String outputDir) {
    for (TestSet test : tests) {
      runTest(test, outputDir);
    }
  }
  
  private static void runTest(TestSet test, String outputDir) {
        
    try {
      Main.main(new String[] { test.getFilePath(), "-o", outputDir, "-m", "-p", "" } );
    } catch (Exception e) {
      e.printStackTrace();
    }
  }

  public static void main(String[] args) {
    
    if (args.length != 2) {
      System.err.println("usage java TestGen <inputfile> <outputdir>");
      System.exit(1);
    }
    //Need output dir
    String inputFile = args[0];
    String outputDir = args[1];
    
    try {
      FileInputStream fis = new FileInputStream(new File(inputFile));
      ANTLRInputStream input = new ANTLRInputStream(fis);
      Lexer lexer = new TestLexer(input);
      CommonTokenStream tokens = new CommonTokenStream(lexer);
      TestParser parser = new TestParser(tokens);
      List<TestSet> tests = parser.tests();
      fis.close();
      
      runTests(tests, outputDir);
      
      generateUnitTests(tests, outputDir);
      
    } catch (IOException ioe) {
      ioe.printStackTrace();
    } catch (RecognitionException re) {
      re.printStackTrace();
    }
  }

  private static void generateUnitTests(List<TestSet> tests, String outputDir) {
    try {
      TestGenerator gen = new TestGenerator(tests);
      gen.generate(new File(outputDir + "/UnitTests.java"), "templates/unittests.vm");
    } catch (Exception e) {
      e.printStackTrace();
    }
  }

}
