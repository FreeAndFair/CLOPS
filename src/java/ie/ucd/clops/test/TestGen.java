package ie.ucd.clops.test;

import ie.ucd.clops.dsl.Main;
import ie.ucd.clops.logging.CLOLogger;

import java.io.File;
import java.io.FileInputStream;
import java.io.IOException;
import java.util.ArrayList;
import java.util.LinkedList;
import java.util.List;
import java.util.logging.Level;

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.Lexer;
import org.antlr.runtime.RecognitionException;

public class TestGen {

  private static void runTests(List<TestSet> tests, File outputDir) {
    for (TestSet test : tests) {
      runTest(test, outputDir);
    }
  }

  private static void runTest(TestSet test, File outputDir) {

    try {
      CLOLogger.setLogLevel(Level.OFF);
      Main.main2(new String[] { test.getInputFileDirPath() + File.separator + test.getFilePath(), "-o", outputDir.getAbsolutePath(), "-m", "-p", "" }, false);
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

    generateTests(new File(inputFile), new File(outputDir));
  }

  public static void generateTests(File inputFile, File outputDir) {
    List<TestSet> testSet = readTestSets(inputFile);
    if (testSet != null) {
      try {
        actuallyGenerateTests(testSet, outputDir);
      } catch (IOException e) {
        e.printStackTrace();
      }
    }
  }
  
  public static void generateTests(List<File> inputFiles, File outputDir) {
    List<TestSet> testSets = new LinkedList<TestSet>();
    for (File inputFile : inputFiles) {
      List<TestSet> testSet = readTestSets(inputFile);
      if (testSet != null) {
        testSets.addAll(testSet);
      }
    }
    
    try {
      actuallyGenerateTests(testSets, outputDir);
    } catch (IOException e) {
      e.printStackTrace();
    }
  }

  private static void actuallyGenerateTests(List<TestSet> testSet, File outputDir) throws IOException {
    runTests(testSet, outputDir);
    testSet = processFileTags(testSet, outputDir);
    generateUnitTests(testSet, outputDir);
  }

  private static List<TestSet> readTestSets(File inputFile) {
    try {
      FileInputStream fis = new FileInputStream(inputFile);
      ANTLRInputStream input = new ANTLRInputStream(fis);
      Lexer lexer = new TestLexer(input);
      CommonTokenStream tokens = new CommonTokenStream(lexer);
      TestParser parser = new TestParser(tokens);
      parser.setInputFileDir(inputFile.getParentFile());
      List<TestSet> tests = parser.tests();
      fis.close();
      return tests;
    } catch (IOException ioe) {
      ioe.printStackTrace();
      return null;
    } catch (RecognitionException re) {
      re.printStackTrace();
      return null;
    }
  }

  //Replace the file tags with actual paths.
  private static List<TestSet> processFileTags(List<TestSet> tests, File outputDir) throws IOException {
    File existingFile = new File(outputDir.getPath() + File.separator + "existing.file");
    existingFile.createNewFile();
    String existingFileString = existingFile.getPath();
    File existingDir = new File(outputDir.getPath() + File.separator + "existing.dir");
    existingDir.mkdir();
    String existingDirString = existingDir.getPath();

    String nonExistantFile = outputDir + File.separator + "asfdshjk.sdfasd";

    List<TestSet> processedTests = new ArrayList<TestSet>(tests.size());
    for (TestSet set : tests) {
      List<TestCase> processedTestCases = new ArrayList<TestCase>(set.getCases().size());
      for (TestCase testCase : set.getCases()) {
        processedTestCases.add(new TestCase(testCase.getCondition(), 
            processInputString(testCase.getTestInput(), existingFileString, existingDirString, nonExistantFile)));
      }
      processedTests.add(new TestSet(set.getInputFileDirPath(), set.getFilePath(), set.getName(), processedTestCases));
    }
    return processedTests;
  }

  private static String processInputString(String input, String existingFile, String existingDir, String nonExistantFile) {
    return input.replaceAll("\\$\\{existing-file\\}", existingFile)
    .replaceAll("\\$\\{existing-dir\\}", existingDir)
    .replaceAll("\\$\\{non-existent-file\\}", nonExistantFile);
  }

  private static void generateUnitTests(List<TestSet> tests, File outputDir) {
    try {
      TestGenerator gen = new TestGenerator(tests);
      gen.generate(new File(outputDir.getPath() + "/UnitTests.java"), "templates/unittests.vm");
    } catch (Exception e) {
      e.printStackTrace();
    }
  }

}
