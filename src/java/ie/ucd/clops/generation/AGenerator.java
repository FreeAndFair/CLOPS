package ie.ucd.clops.generation;

import ie.ucd.clops.dsl.OptionType;
import ie.ucd.clops.dsl.structs.BasicOptionDescription;
import ie.ucd.clops.dsl.structs.DSLInformation;
import ie.ucd.clops.logging.CLOLogger;
import ie.ucd.clops.runtime.options.CLOPSErrorOption;
import ie.ucd.clops.util.StringUtil;

import java.io.File;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.InputStreamReader;
import java.io.LineNumberReader;
import java.io.PrintStream;
import java.io.Reader;
import java.util.Properties;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.apache.velocity.Template;
import org.apache.velocity.VelocityContext;
import org.apache.velocity.app.Velocity;
import org.apache.velocity.exception.ParseErrorException;
import org.apache.velocity.exception.ResourceNotFoundException;

public abstract class AGenerator {
  /** The templates directory: "templates/". */
  public static final String TEMPLATE_BASE = "templates" + File.separator;
  
  /** the context used for velocity. */
  private VelocityContext context;


  /**
   * Creates a generator from the collected DSL informations.
   * @param infos the informations from the DSL
   * @throws Exception in case the initialisation of Velocity fails
   */
  public AGenerator(final DSLInformation infos) throws Exception {
    Velocity.init(configureVelocityLoader());
    context = createContext(infos);
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
   * Define the context for document generation.
   * @param infos the informations gathered by the parsing of the dsl.
   * @return Context for DSL information
   */
  public VelocityContext createContext(final DSLInformation infos) {
    final VelocityContext ctxt = new VelocityContext();
    ctxt.put("info", infos);
    ctxt.put("Boolean", Boolean.class);
    ctxt.put("StringUtil", StringUtil.class);
    ctxt.put("BasicOptionDescription", BasicOptionDescription.class);
    ctxt.put("CLOPSErrorOption", CLOPSErrorOption.class);
    ctxt.put("OptionType", OptionType.class);
    ctxt.put("CodeGenerator", CodeGenerator.class);
    return ctxt;
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
  protected final void generate(final File output,
                       final String templateFileName,
                       final String explanationText) {
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
        final InputStreamReader reader = 
          new InputStreamReader(template.getResourceLoader().getResourceStream(templateFile));
        final File outputFile = getOutputFile(output, template.getName(), reader);

        final FileWriter writer = new FileWriter(outputFile);

        template.merge(context, writer);
        writer.close();
        logger.log(Level.INFO,
                   "Successfully created " + outputFile.getPath());
      }
      catch (Exception e) { 
        /* e can be of the following types:
           IOException FileNotFoundException MethodInvocationException 
           ParseErrorException ResourceNotFoundException
         */
        logger.log(Level.WARNING,
                   explanationText + " failed: " + e.getLocalizedMessage());
      }
    }
    else {
      logger.log(Level.SEVERE,
                 "Error, template not found: " + templateFile);
    }

  }

  private File getOutputFile(File output, String name, Reader template) throws ResourceNotFoundException, ParseErrorException, Exception {

    if (output.isDirectory()) {
      LineNumberReader lnr = new LineNumberReader(template);
      final String first = lnr.readLine();
      if (first.startsWith("##!")) {
        final File tmp1 = File.createTempFile("clops", ".tmp", output);
        tmp1.deleteOnExit();
        final File tmp2 = File.createTempFile("clops", ".tmp", output);
        tmp2.deleteOnExit();
        final PrintStream strm = new PrintStream(new FileOutputStream(tmp1));
        strm.println(first.substring("##!".length()));
        strm.close();
        final Template plate = Velocity.getTemplate(tmp1.getAbsolutePath());
        final FileWriter writer = new FileWriter(tmp2);
        plate.merge(context, writer);
        writer.close();
        lnr = new LineNumberReader(new FileReader(tmp2));
        final String tput = lnr.readLine().trim();
        lnr.close();
        return new File(output, tput);
      } 
      else {
        if (name.endsWith(".vm")) {
          return new File(output,
                          name.substring(0, name.length() - ".vm".length()));
        } 
        else { // we hope that the user knows what he's doing
          //ok - that's a bit presomptuous
          return new File(output, name);
        }
      }
    }
    return output;
  }

}
