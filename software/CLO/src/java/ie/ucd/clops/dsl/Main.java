package ie.ucd.clops.dsl;

import ie.ucd.clops.codegeneration.CodeGenerator;
import ie.ucd.clops.documentation.DocumentGenerator;
import ie.ucd.clops.dsl.generatedinterface.CLODSLOptionStore;
import ie.ucd.clops.dsl.generatedinterface.CLODSLOptionsInterface;
import ie.ucd.clops.dsl.generatedinterface.CLODSLParser;
import ie.ucd.clops.dsl.parser.CLOLexer;
import ie.ucd.clops.dsl.parser.CLOParser;
import ie.ucd.clops.logging.CLOLogger;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.logging.Level;

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;


/**
 * 
 * @author Fintan
 *
 */
public class Main {

  /** The main method of this project, runs the dsl parser, followed by the code generator.
   *  The arguments are parser according to the CLODSLParser, which is generated from the file clo-dsl.clo.
   *  See also the target update-dslcli in the build file.
   *  @param args the arguments to the program.
   */
  public static void main(String[] args) {
    try {
      CLODSLParser parser = new CLODSLParser();
      boolean success = parser.parse(args);
      if (success) {
        CLODSLOptionStore options = parser.getOptionStore();
        execute(options);
      } else {
        //Just end?
        CLOLogger.getLogger().log(
          Level.SEVERE, "Format:" + parser.getFormatString());
        CLOLogger.getLogger().log(Level.SEVERE, "Fail!");
        return;
      }
    } catch (InvalidOptionPropertyValueException e) {
      e.printStackTrace();
      CLOLogger.getLogger().log(Level.SEVERE, "Error setting initial property values for options.");
    }
  }
  
  /**
   * Run the dsl parser and code generator. The options supplied will in particular indicate
   * the input file to be used and the output location for the generated code.
   * @param options the parsed options to use for running the program.
   */
  public static boolean execute(CLODSLOptionsInterface options) {
    
    //No need to check if each of these are set, as this is enforced by the parser, validity checker, etc.
    File inputFile = options.getinput();
    File outputDir = options.getoutput();
    
    if (options.isoption_factorySet()) {
      setOptionTypeFactory(options.getoption_factory());
    }
    
    CLOParser parser = null;
    try {
      CLOLexer lexer = new CLOLexer(new ANTLRInputStream(new FileInputStream(inputFile)));
      parser = new CLOParser(new CommonTokenStream(lexer));

      parser.prog();

      if (parser.isValidParse()) {
        CLOLogger.getLogger().log(Level.INFO, "Successfully parsed dsl file!");

        //Make sure no newlines in the format string. This should probably be done whilst processing the DSL
        parser.getDslInformation().setFormatString(parser.getDslInformation().getFormatString().replaceAll("\\n", " "));
        
        //Override package name from commandline
        if (options.isoutput_packageSet()) {
          parser.getDslInformation().setPackageName(options.getoutput_package());
        }
        boolean genTest = options.isgen_testSet() && options.getgen_test();
        CodeGenerator.createCode(parser.getDslInformation(), outputDir, genTest);
        
        CLOLogger.getLogger().log(Level.INFO, "Created code in " + outputDir.getAbsolutePath());
      
        // Generate Documentation
        DocumentGenerator documentation = new DocumentGenerator(parser.getDslInformation());
	    documentation.generate ("help.txt", DocumentGenerator.HELP_TEMPLATE);
		documentation.generate ("help.html", DocumentGenerator.HTML_TEMPLATE);
        
        return true;
      } else {
        CLOLogger.getLogger().log(Level.SEVERE, "Did not parse successfully.");
        if (parser.getCustomErrorMessage() != null) {
          CLOLogger.getLogger().log(Level.SEVERE, parser.getCustomErrorMessage());
        }
      }
      
    } catch (FileNotFoundException e) {
      //Shouldn't really happen as we check this in the Option
      CLOLogger.getLogger().log(Level.SEVERE, "Input file not found: " + inputFile);
    } catch (IOException e) {
      CLOLogger.getLogger().log(Level.SEVERE, "I/O error whilst processing input file: " + inputFile);
    } catch (RecognitionException e) {
      CLOLogger.getLogger().log(Level.SEVERE, "Caught recognition error");
      if (parser.getCustomErrorMessage() != null) {
        CLOLogger.getLogger().log(Level.SEVERE, parser.getCustomErrorMessage());
      }
    } catch (Exception e) {
		// TODO Auto-generated catch block
		e.printStackTrace();
	}
    return false;
  }
  
  /** 
   * Instantiate the {@code OptionTypeFactory} with a given class. The provided class must be present on the 
   * classpath.
   * @param factoryName the fully qualified name of the class that is to be used as a {@code OptionTypeFactory} 
   */
  private static void setOptionTypeFactory(String factoryName) {
    try {
      Class<?> c = Class.forName(factoryName);

      Constructor<?>[] constructors = c.getConstructors();
      assert constructors.length == 1;
      Constructor<?> constructor = constructors[0];

      Object o = constructor.newInstance();

      OptionTypeFactory factory = (OptionTypeFactory)o;
      OptionTypeFactory.setOptionTypeFactory(factory);
      CLOLogger.getLogger().log(Level.INFO, "Successfully using custom option factory " + factoryName);
      return;
      
    } catch (ClassNotFoundException e) {
      CLOLogger.getLogger().log(Level.WARNING, "No class on classpath with name " + factoryName);
    } catch (IllegalArgumentException e) {
      CLOLogger.getLogger().log(Level.WARNING, "An error occurred when loading the factory " + factoryName);
    } catch (InstantiationException e) {
      CLOLogger.getLogger().log(Level.WARNING, "An error occurred when loading the factory " + factoryName);
    } catch (IllegalAccessException e) {
      CLOLogger.getLogger().log(Level.WARNING, "An error occurred when loading the factory " + factoryName);
    } catch (InvocationTargetException e) {
      CLOLogger.getLogger().log(Level.WARNING, "An error occurred when loading the factory " + factoryName);
    } catch (ClassCastException e) {
      CLOLogger.getLogger().log(Level.WARNING, "Factory specified is not a valid OptionTypeFactory " + factoryName);
    }
  }
  
}
