package ie.ucd.clops.documentation;

import ie.ucd.clops.dsl.structs.BasicOptionDescription;
import ie.ucd.clops.dsl.structs.DSLInformation;
import ie.ucd.clops.dsl.structs.OptionDescription;

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

public class DocumentGenerator {

  public static final String HTML_TEMPLATE = "templates/html.vm";
  public static final String HELP_TEMPLATE = "templates/help.vm";
  private VelocityContext context;

  public DocumentGenerator(DSLInformation information) throws Exception {
    Velocity.init();
    context = createContext(information);	
  }

  /**
   * 
   * @param filename
   * @param templateName
   * @throws Exception
   * 
   * <JML>
   *   requires velocity.templateExists(templateName);
   * </JML>
   */
  public void generate(String filename, String templateName) throws Exception {


    if (Velocity.resourceExists(templateName)) {
      Template template = Velocity.getTemplate(templateName);

      PrintStream printStream = new PrintStream(filename);

      Writer writer = new java.io.OutputStreamWriter(printStream);

      template.merge(context, writer);

      writer.flush();
      writer.close();
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
      documentation.generate ("help.txt", HELP_TEMPLATE);
      documentation.generate ("help.html", HTML_TEMPLATE);
    } catch (Exception e) {
      e.printStackTrace();
    }

    logfile.println("Finished document generation");
  }

}
