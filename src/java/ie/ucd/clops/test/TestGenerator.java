package ie.ucd.clops.test;

import ie.ucd.clops.logging.CLOLogger;

import java.io.File;
import java.io.FileWriter;
import java.util.List;
import java.util.Properties;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.apache.velocity.Template;
import org.apache.velocity.VelocityContext;
import org.apache.velocity.app.Velocity;


public class TestGenerator {

  VelocityContext context;
  final List<TestSet> tests;
  
  public TestGenerator(List<TestSet> tests, boolean logFine) throws Exception {
    this.tests = tests;
    init(logFine);
    Velocity.init(configureVelocityLoader());
  }
  
  private void init(boolean logFine) {
    context = new VelocityContext();
    //context.put("CodeGenerator", CodeGenerator.class);
    context.put("tests", tests);
    context.put("logFine", logFine);
  }
  
  /**
   * Configures the velocity loader with the necessary properties.
   * @return A propery file containing all the informations
   */
  private static Properties configureVelocityLoader() {
    final Properties prop = new Properties();
    prop.put("resource.loader", "file, class");
    prop.put("class.resource.loader.description",
             "Velocity Classpath Resource Loader");
    prop.put("class.resource.loader.class",
             "org.apache.velocity.runtime.resource.loader." +
             "ClasspathResourceLoader");
    prop.put("file.resource.loader.description",
             "Velocity File Resource Loader");
    prop.put("file.resource.loader.class",
             "org.apache.velocity.runtime.resource.loader.FileResourceLoader");
    prop.put("file.resource.loader.path", "");

    return prop;
  }
  
  /**
   * Generates a file from a template, in the specified output.
   *
   * @param output if it is a directory, gets the name of the file from the
   * template file
   * @param templateFileName the name of the template file that is being used
   * @param explanationText text used for error reporting
   *
   * <JML>
   *   requires velocity.resourceExists(templateName);
   * </JML>
   */
  public final void generate(final File output,
                       final String templateFileName) {
    String templateFile;
    final Logger logger = CLOLogger.getLogger();
    if (Velocity.resourceExists(templateFileName)) {
      templateFile = templateFileName;
    } 
    else {
      templateFile = new File(templateFileName).getAbsolutePath();
      //we're feeling lucky
    }
    
    if (Velocity.resourceExists(templateFile)) {
      try {
        final Template template = Velocity.getTemplate(templateFile);
        final FileWriter writer = new FileWriter(output);
        template.merge(context, writer);
        writer.close();
        logger.log(Level.INFO,
                   "Successfully created " + output.getPath());
      }
      catch (Exception e) { 
        /* e can be of the following types:
           IOException FileNotFoundException MethodInvocationException 
           ParseErrorException ResourceNotFoundException
         */
        logger.log(Level.WARNING,
                   "failed:" + e.getLocalizedMessage());
      }
    }
    else {
      logger.log(Level.SEVERE,
                 "Error, template not found: " + templateFile);
    }

  }

}
