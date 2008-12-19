package ie.ucd.clops.documentation;

import ie.ucd.clops.dsl.structs.BasicOptionDescription;
import ie.ucd.clops.dsl.structs.DSLInformation;
import ie.ucd.clops.dsl.structs.OptionDescription;
import ie.ucd.clops.logging.CLOLogger;

import java.io.FileNotFoundException;
import java.io.IOException;
import java.io.PrintStream;
import java.io.Writer;
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
		Velocity.init();
		context = createContext(information);
	}

	/**
	 * Generate command line options help documentation from DSL information using template.
	 * 
	 * @param filename The filename of the document to be created
	 * @param templateName The template from which to create the document
	 */
	public void generate(String filename, String templateName) {

		if (Velocity.resourceExists(templateName)) {
			try {
				Template template = Velocity.getTemplate(templateName);

				PrintStream printStream = new PrintStream(filename);

				Writer writer = new java.io.OutputStreamWriter(printStream);

				template.merge(context, writer);

				writer.flush();
				writer.close();
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
			CLOLogger.getLogger().log(Level.WARNING,
			    "Unable to find resource for document generation template in " + templateName);
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
			documentation.generate("help.txt", HELP_TEMPLATE);
			documentation.generate("help.html", HTML_TEMPLATE);
		} catch (Exception e) {
			e.printStackTrace();
		}

		logfile.println("Finished document generation");
	}

}
