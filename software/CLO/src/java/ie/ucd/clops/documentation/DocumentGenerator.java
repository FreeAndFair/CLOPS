package ie.ucd.clops.documentation;

import ie.ucd.clops.dsl.structs.BasicOptionDescription;
import ie.ucd.clops.dsl.structs.DSLInformation;
import ie.ucd.clops.logging.CLOLogger;
import ie.ucd.clops.util.StringUtil;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.LineNumberReader;
import java.io.PrintStream;
import java.util.Properties;
import java.util.logging.Level;
import java.util.logging.Logger;

import org.apache.velocity.Template;
import org.apache.velocity.VelocityContext;
import org.apache.velocity.app.Velocity;
import org.apache.velocity.exception.MethodInvocationException;
import org.apache.velocity.exception.ParseErrorException;
import org.apache.velocity.exception.ResourceNotFoundException;

/**
 * <BON>
 * class_chart DOCUMENT_GENERATION
 * explanation
 *   "Generation of documentation from the descriptions of options"
 * command
 *   "Generate Documentation"
 * end
 * </BON>
 */

public class DocumentGenerator {

  public static final String HTML_TEMPLATE = "templates/html.vm";
  public static final String HELP_TEMPLATE = "templates/help.vm";
  private VelocityContext context;


  public DocumentGenerator(DSLInformation information) throws Exception {
    Velocity.init(configureVelocityLoader());
    context = createContext(information);
  }

  private static Properties configureVelocityLoader() {
    Properties prop = new Properties();
    prop.put("resource.loader", "file, class");
    prop.put("class.resource.loader.description",
             "Velocity Classpath Resource Loader");
    prop.put("class.resource.loader.class",
             "org.apache.velocity.runtime.resource.loader.ClasspathResourceLoader");
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
   * @param templateFileName
   * @param explanationText text used for error reporting
   *
   * <JML>
   *   requires velocity.resourceExists(templateName);
   * </JML>
   */
  public final void generate(final File output,
                       final String templateFileName,
                       final String explanationText) {
    String templateFile;
    Logger logger = CLOLogger.getLogger();
    if (Velocity.resourceExists(templateFileName)) {
      templateFile = templateFileName;
    } else {
      templateFile = new File(templateFileName).getAbsolutePath();
      //we're feeling lucky
    }

    if (Velocity.resourceExists(templateFile)) {

      try {
        Template template = Velocity.getTemplate(templateFile);
        File outputFile = getOutputFile(output, templateFile);
        FileWriter writer = new FileWriter(outputFile);
        template.merge(context, writer);
        writer.close();
        logger.log(Level.INFO,
                   "Successfully created " + outputFile.getPath());
      } catch (ResourceNotFoundException e) {
        logger.log(Level.WARNING,
                   explanationText + "" + " failed:" + e.getLocalizedMessage());
      } catch (ParseErrorException e) {
        logger.log(Level.WARNING,
                   explanationText + " failed:" + e.getLocalizedMessage());
      } catch (MethodInvocationException e) {
        logger.log(Level.WARNING,
                   explanationText + " failed:" + e.getLocalizedMessage());
      } catch (FileNotFoundException e) {
        logger.log(Level.WARNING,
                   explanationText + " failed:" + e.getLocalizedMessage());
      } catch (IOException e) {
        logger.log(Level.WARNING,
                   explanationText + " failed:" + e.getLocalizedMessage());
      } catch (Exception e) {
        logger.log(Level.WARNING,
                   explanationText + " failed:" + e.getLocalizedMessage());
      }
    } else {
      logger.log(Level.SEVERE,
                 "Error, template not found: " + templateFile);
    }

  }

  private File getOutputFile(File output, String template) throws ResourceNotFoundException, ParseErrorException, Exception {
    File templateFile = new File(template);
    if (output.isDirectory()) {
      LineNumberReader lnr = new LineNumberReader(new FileReader(templateFile));
      String first = lnr.readLine();
      if (first.startsWith("##!")) {
        File tmp1 = File.createTempFile("clops", ".tmp", output);
        tmp1.deleteOnExit();
        File tmp2 = File.createTempFile("clops", ".tmp", output);
        tmp2.deleteOnExit();
        PrintStream strm = new PrintStream(new FileOutputStream(tmp1));
        strm.println(first.substring("##!".length()));
        strm.close();
        Template plate = Velocity.getTemplate(tmp1.getAbsolutePath());
        FileWriter writer = new FileWriter(tmp2);
        plate.merge(context, writer);
        writer.close();
        lnr = new LineNumberReader(new FileReader(tmp2));
        String tput = lnr.readLine().trim();
        lnr.close();
        return new File(output, tput);
      }
      else {
        String name = templateFile.getName();
        return new File(output, name.substring(0, name.length() - ".vm".length()));
      }
    }
    return output;
  }

  

  /**
   * Define the context for document generation.
   *
   * @return Context for DSL information
   */
  protected VelocityContext createContext(final DSLInformation info) {
    final VelocityContext context = new VelocityContext();
    context.put("info", info);
    context.put("StringUtil", StringUtil.class);
    context.put("BasicOptionDescription", BasicOptionDescription.class);
    return context;
  }


}
