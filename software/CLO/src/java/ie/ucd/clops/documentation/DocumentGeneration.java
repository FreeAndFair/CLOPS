package ie.ucd.clops.documentation;

import java.io.Writer;

import org.apache.velocity.Template;
import org.apache.velocity.VelocityContext;
import org.apache.velocity.app.Velocity;

/**
 * <BON>
 * class_chart DOCUMENT_GENERATION 
 *   explanation "Generation of documentation from the descriptions of options"
 *  end
 * </BON>
 */

public class DocumentGeneration {

	public void generate() {
		try {
			Velocity.init();

			VelocityContext context = new VelocityContext();

			context.put("option", new OptionDescription());

			Template template = Velocity.getTemplate("html.vm");

			Writer writer = new java.io.OutputStreamWriter(System.out);

			template.merge(context, writer);

			writer.flush();
			writer.close();

		} catch (Exception e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}

	}

}
