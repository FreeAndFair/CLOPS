package ie.ucd.clops.test;

import ie.ucd.clops.test.generatedinterface.CLOTestOptionsInterface;
import ie.ucd.clops.test.generatedinterface.CLOTestParser;

import java.io.File;
import java.io.FilenameFilter;
import java.net.URL;
import java.net.URLClassLoader;
import java.util.List;

import org.junit.runner.JUnitCore;

public class Main {

  /**
   * @param args the arguments from the command line.
   */
  public static void main(final String[] args) {
    try {
      CLOTestParser parser = new CLOTestParser();
      
      if (parser.parse(args)) {
        execute(parser.getOptionStore());
      } else {
        //TODO print usage  
        System.out.println("Invalid arguments.");
        return;
      }
      
    } catch (Exception e) {

    }
  }
  
  private static void execute(CLOTestOptionsInterface options) {
    List<File> inputFiles = options.getInput();
    File outputDir = options.getOutput();
    
    generateTests(inputFiles, outputDir);
    
    if (options.getRunTests()) {
      compileTests(outputDir);
      runTests(outputDir);
    }
  }

  
  private static void generateTests(List<File> inputFiles, File outputDir) {
    TestGen.generateTests(inputFiles, outputDir);
  }

  private static boolean compileTests(File outputDir) {
    String[] sourceFiles = outputDir.list(new FilenameFilter() {
      @Override
      public boolean accept(File dir, String name) {
        return name.endsWith(".java");
      }      
    });
    
    ClassLoader loader = ClassLoader.getSystemClassLoader();
    if (loader instanceof URLClassLoader) {
    
      
      String[] args = new String[sourceFiles.length + 2];
      args[0] = "-cp";
      args[1] = getClassPath((URLClassLoader)loader); 
      System.out.println("Path: " + args[1]);
      
      
      for (int i=0; i < sourceFiles.length; i++) {
        args[i+2] = outputDir.getPath() + File.separator + sourceFiles[i];
      }
      
      int result = com.sun.tools.javac.Main.compile(args);
      return result == 0;
    } else {
      System.out.println("Not an URLClassLoader, cannot extract existing classpath to compile automatically.");
      return false;
    }
  }
  
  private static String getClassPath(URLClassLoader loader) {
    URL[] urls = loader.getURLs();
    StringBuilder path = new StringBuilder();
    for (URL url : urls) {
      path.append(url.getPath());
      path.append(File.pathSeparator);
    }
    return path.toString();
  }
  
  private static void runTests(File outputDir) {
    System.out.println("Running tests");
    JUnitCore.main("UnitTests");  
  }
  
}
