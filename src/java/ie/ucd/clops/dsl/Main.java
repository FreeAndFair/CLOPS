package ie.ucd.clops.dsl;

import ie.ucd.clops.dsl.generatedinterface.CLODSLOptionStore;
import ie.ucd.clops.dsl.generatedinterface.CLODSLOptionsInterface;
import ie.ucd.clops.dsl.generatedinterface.CLODSLParser;
import ie.ucd.clops.dsl.parser.CLOLexer;
import ie.ucd.clops.dsl.parser.CLOParser;
import ie.ucd.clops.dsl.structs.DSLInformation;
import ie.ucd.clops.generation.CodeGenerator;
import ie.ucd.clops.generation.DocumentGenerator;
import ie.ucd.clops.logging.CLOLogger;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.antlr.runtime.ANTLRFileStream;
import org.antlr.runtime.CharStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;


/**
 * The main entry point of CLOPS.
 * @author Fintan
 */
public class Main {

  /** 
   * The main method of this project, runs the dsl parser, 
   * followed by the code generator.
   * The arguments are parser according to the CLODSLParser, 
   * which is generated from the file clo-dsl.clo.
   * See also the target update-dslcli in the build file.
   * @param args the arguments to the program.
   */
  public static void main(final String[] args) throws Exception {
    try {
      final CLODSLParser parser = new CLODSLParser();
      final boolean success = parser.parse(args);
      if (success) {
        final CLODSLOptionStore options = parser.getOptionStore();
        execute(options);
      } 
      else {
        //Just end?
        CLOLogger.getLogger().log(
          Level.SEVERE, "Format:" + parser.getFormatString());
        CLOLogger.getLogger().log(Level.SEVERE, "Fail!");
        return;
      }
    } 
    catch (InvalidOptionPropertyValueException e) {
      e.printStackTrace();
      CLOLogger.getLogger().log(Level.SEVERE, 
                                "Error setting initial property values for options.");
    }
  }
  
  /**
   * Run the dsl parser and code generator. The options supplied will in particular indicate
   * the input file to be used and the output location for the generated code.
   * @param options the parsed options to use for running the program.
   */
  public static boolean execute(final CLODSLOptionsInterface options) {
    if (options.isVerboseSet() && options.getVerbose()) {
      CLOLogger.setLogLevel(Level.FINE);
    }

    /* No need to check if each of these are set, as this is 
       enforced by the parser, validity checker, etc. */
    final File input = options.getInput();
    final File output = options.getOutput();
    
    if (options.isOptionFactorySet()) {
      setOptionTypeFactory(options.getOptionFactory());
    }

    final DSLInformation infos = parseFile(input);
    if (infos == null) {
      return false;
    }
    infos.TRANSITIVE_FLYRULES =
      options.isTransitiveFlyRulesSet() &&  options.getTransitiveFlyRules();
    /* Make sure no newlines in the format string. 
       This should probably be done whilst processing the DSL */
    infos.setFormatString(infos.getFormatString().replaceAll("\\n", " "));
    
    //Override package name from commandline
    if (options.isOutputPackageSet()) {
      infos.setPackageName(options.getOutputPackage());
    }
    infos.processPlaceholders();
    CodeGenerator code = null;
    DocumentGenerator docs = null;
    try {
      code = new CodeGenerator(infos);
      docs = new DocumentGenerator(infos);
    }
    catch (Exception e) {
      CLOLogger.getLogger().log(Level.SEVERE,
                                "Something went wrong in the initialisation" +
                                " of the generators. " + e);
    }
    
    final boolean genTest = options.isTestSet() && options.getTest();

    code.createCode(output, genTest);
    CLOLogger.getLogger().log(Level.INFO, 
                              "Created code in " + output.getAbsolutePath());    

    if (options.isDocsSet() || 
        options.isBuiltinSet() || 
        options.isCustomSet()) {
      // we are doing some template generation
      
      final File target = getTemplateTarget(options);
      
      // Generate Documentation
      if (options.isDocsSet()) {
        docs.generateDefault(target);
      }
      if (options.isBuiltinSet()) {
        docs.generateBuiltin(target, options.getBuiltin());
      }
      if (options.isCustomSet()) {
        docs.generateCustom(target, options.getCustom());
      }
    }
    
    return true;
   
  }
  
  private static File getTemplateTarget(CLODSLOptionsInterface options) {
    if (options.isTargetSet()) {
      return options.getTarget();
    }
    return new File("");
  }

  /** 
   * Instantiate the {@code OptionTypeFactory} with a given class. 
   * The provided class must be present on the classpath.
   * @param factoryName the fully qualified name of the class 
   * that is to be used as a {@code OptionTypeFactory} 
   */
  private static void setOptionTypeFactory(final String factoryName) {
    final Logger logger = CLOLogger.getLogger();
    try {
      final Class<?> c = Class.forName(factoryName);
      final Constructor<?>[] constructors = c.getConstructors();
      assert constructors.length == 1;
      final Constructor<?> constructor = constructors[0];
      final Object o = constructor.newInstance();
      if (o instanceof OptionTypeFactory) {
        final OptionTypeFactory factory = (OptionTypeFactory)o;
        OptionTypeFactory.setOptionTypeFactory(factory);
        logger.log(Level.INFO,
                   "Successfully using custom option factory " + factoryName);
      }
      else {
        logger.log(Level.WARNING, 
                   "Factory specified is not a valid OptionTypeFactory " + factoryName);
      }
      return;
      
    } 
    catch (ClassNotFoundException e) {
      logger.log(Level.WARNING, 
                 "No class on classpath with name " + factoryName);
    } 
    catch (IllegalArgumentException e) {
      logger.log(Level.WARNING, 
                 "An error occurred when loading the factory " + factoryName);
    } 
    catch (InstantiationException e) {
      logger.log(Level.WARNING, 
                 "An error occurred when loading the factory " + factoryName);
    } 
    catch (IllegalAccessException e) {
      logger.log(Level.WARNING, 
                 "An error occurred when loading the factory " + factoryName);
    }
    catch (InvocationTargetException e) {
      logger.log(Level.WARNING, 
                 "An error occurred when loading the factory " + factoryName);
    }
  }
  
  
  public static DSLInformation parseFile(final File input) { 
    try {

      final CharStream cs = new ANTLRFileStream(input.getAbsolutePath());
      final CLOLexer cl = new CLOLexer(cs);
      final CLOParser parser = new CLOParser(new CommonTokenStream(cl));
      try {
        parser.prog();
      }
      catch (RecognitionException e) {
        CLOLogger.getLogger().log(Level.SEVERE, "Caught recognition error");
      }   
      if (parser.isValidParse()) {
        CLOLogger.getLogger().log(Level.INFO, "Successfully parsed dsl file!");
        return parser.getDslInformation();
      }
      CLOLogger.getLogger().log(Level.SEVERE, "Did not parse successfully.");
      if (parser.getCustomErrorMessage() != null) {
        CLOLogger.getLogger().log(Level.SEVERE, parser.getCustomErrorMessage());
      }
    }
    catch (FileNotFoundException e) {
      //Shouldn't really happen as we check this in the Option
      CLOLogger.getLogger().log(Level.SEVERE, 
                                "Input file not found: " + input);
    } 
    catch (IOException e) {
      CLOLogger.getLogger().log(Level.SEVERE, 
                                "I/O error whilst processing input file: " + 
                                input);
    }
    return null;
  }
}
