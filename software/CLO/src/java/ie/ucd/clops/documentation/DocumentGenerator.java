package ie.ucd.clops.documentation;

import ie.ucd.clops.dsl.structs.BasicOptionDescription;
import ie.ucd.clops.dsl.structs.DSLInformation;
import ie.ucd.clops.dsl.structs.OptionDescription;
import ie.ucd.clops.logging.CLOLogger;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileWriter;
import java.io.IOException;
import java.io.PrintStream;
import java.util.Properties;
import java.util.logging.Level;

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
    prop.put("class.resource.loader.description", "Velocity Classpath Resource Loader");
    prop.put("class.resource.loader.class", "org.apache.velocity.runtime.resource.loader.ClasspathResourceLoader");
    prop.put("file.resource.loader.description", "Velocity File Resource Loader");
    prop.put("file.resource.loader.class", "org.apache.velocity.runtime.resource.loader.FileResourceLoader");
    prop.put("file.resource.loader.path", "");
    return prop;
  }

  /**
   * 
   * @param filename
   * @param templateName
   * @throws Exception
   * 
   * <JML>
   *   requires velocity.resourceExists(templateName);
   * </JML>
   */
  public void generate(File outputFile, String templateFile) {

    if (Velocity.resourceExists(templateFile)) {

      try {
        Template template = Velocity.getTemplate(templateFile);
        FileWriter writer = new FileWriter(outputFile);

        template.merge(context, writer);
        writer.flush();
        writer.close();
        CLOLogger.getLogger().log(Level.INFO, "Successfully created documentation " + outputFile.getPath());

      } catch (ResourceNotFoundException e) {
        CLOLogger.getLogger().log(Level.WARNING,"Document generation failed:" + e.getLocalizedMessage());
      } catch (ParseErrorException e) {
        CLOLogger.getLogger().log(Level.WARNING,"Document generation failed:" + e.getLocalizedMessage());
      } catch (MethodInvocationException e) {
        CLOLogger.getLogger().log(Level.WARNING,"Document generation failed:" + e.getLocalizedMessage());
      } catch (FileNotFoundException e) {
        CLOLogger.getLogger().log(Level.WARNING,"Document generation failed:" + e.getLocalizedMessage());
      } catch (IOException e) {
        CLOLogger.getLogger().log(Level.WARNING,"Document generation failed:" + e.getLocalizedMessage());
      } catch (Exception e) {
        CLOLogger.getLogger().log(Level.WARNING,"Document generation failed:" + e.getLocalizedMessage());
      }
    } else {
      CLOLogger.getLogger().log(Level.SEVERE, "Error, template not found: " + templateFile);
    }

  }
    
	/**
	 * Define the context for document generation
	 * 
	 * @return Context for DSL information
	 */
	protected VelocityContext createContext(DSLInformation information) {
		VelocityContext context = new VelocityContext();

		context.put("information", information);
		return context;
	}

	/**
	 * Test document generation
	 */
	public static void main(String[] args) {

		PrintStream logfile = System.out;

		logfile.println("Starting document generation");

		DSLInformation information = new DSLInformation();
		information.setPackageName("TEST");
		OptionDescription optionDescription = new BasicOptionDescription();
		optionDescription.setId("Option 1");
		information.addOptionDescription(optionDescription);
		optionDescription.setId("Option 2");
		information.addOptionDescription(optionDescription);
		information.setParserName("Parser");

		try {
			DocumentGenerator documentation = new DocumentGenerator(information);
//			documentation.generate("help.txt", HELP_TEMPLATE);
//			documentation.generate("help.html", HTML_TEMPLATE);
		} catch (Exception e) {
			e.printStackTrace();
		}

		logfile.println("Finished document generation");
	}

}
