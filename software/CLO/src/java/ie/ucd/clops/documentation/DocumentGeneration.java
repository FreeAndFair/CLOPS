package ie.ucd.clops.documentation;

import java.io.OutputStream;
import java.io.PrintStream;
import java.io.Writer;

import org.apache.velocity.Template;
import org.apache.velocity.VelocityContext;
import org.apache.velocity.app.Velocity;

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

public class DocumentGeneration {

	public static final String HTML_TEMPLATE_NAME = "html.vm";

	public void generate(OutputStream targetFile) {
		try {
			Velocity.init();

			VelocityContext context = createContext();

			Template template = Velocity.getTemplate(DocumentGeneration.HTML_TEMPLATE_NAME);

			Writer writer = new java.io.OutputStreamWriter(targetFile);

			template.merge(context, writer);

			writer.flush();
			writer.close();

		} catch (Exception e) {
			// @TODO log this
			e.printStackTrace();
		}

	}

	/**
	 * Define the context for document generation
	 * 
	 * @return
	 */
	protected VelocityContext createContext() {
		VelocityContext context = new VelocityContext();

		context.put("option", new OptionDescription());
		return context;
	}

}
