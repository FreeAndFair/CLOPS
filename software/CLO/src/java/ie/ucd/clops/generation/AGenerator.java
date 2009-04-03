package ie.ucd.clops.generation;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.FileReader;
import java.io.FileWriter;
import java.io.IOException;
import java.io.LineNumberReader;
import java.io.PrintStream;
import java.util.LinkedList;
import java.util.List;
import java.util.Properties;
import java.util.logging.Level;
import java.util.logging.Logger;

import ie.ucd.clops.dsl.OptionType;
import ie.ucd.clops.dsl.structs.BasicOptionDescription;
import ie.ucd.clops.dsl.structs.DSLInformation;
import ie.ucd.clops.logging.CLOLogger;
import ie.ucd.clops.runtime.options.CLOPSErrorOption;
import ie.ucd.clops.util.StringUtil;

import org.apache.velocity.Template;
import org.apache.velocity.VelocityContext;
import org.apache.velocity.app.Velocity;
import org.apache.velocity.exception.MethodInvocationException;
import org.apache.velocity.exception.ParseErrorException;
import org.apache.velocity.exception.ResourceNotFoundException;

public abstract class AGenerator {
  /** the context used for velocity. */
  private VelocityContext context;

  /** The templates directory: "templates/". */
  public static final String TEMPLATE_BASE = "templates" + File.separator;


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
    Properties prop = new Properties();
    prop.put("resource.loader", "file, class");
    prop.put("class.resource.loader.description",
             "Velocity Classpath Resource Loader");
    prop.put("class.resource.loader.class",
             "org.apache.velocity.runtime.resource.loader."
             + "ClasspathResourceLoader");
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
    ctxt.put("StringUtil", StringUtil.class);
    ctxt.put("BasicOptionDescription", BasicOptionDescription.class);
    ctxt.put("CLOPSErrorOption", CLOPSErrorOption.class);
    ctxt.put("OptionType", OptionType.class);
    ctxt.put("CodeGenerator", CodeGenerator.class);
    return ctxt;
  }

  /**
   * Produces java String constant containing a given String
   * that may contain newlines.
   * @param s
   * TODO: move to String util
   */
  public static List<String> quoteMultilineString(final String s) {
    final String[] lines = s.split("\n");
    final List<String> result = new LinkedList<String>();

    for (String line : lines) {
      line = line.trim();
      if (line.equals("")) {
        continue;
      }
      result.add(line);
    }
    if (result.size() == 0) {
      result.add("\"\"");
    }
    return result;
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
      } else {
        String name = templateFile.getName();
        if (name.endsWith(".vm")) {
          return new File(output,
                          name.substring(0, name.length() - ".vm".length()));
        } else { // we hope that the user knows what he's doing
          //ok - that's a bit presomptuous
          return new File(output, name);
        }
      }
    }
    return output;
  }

}
