package ie.ucd.clops.generation;

import ie.ucd.clops.dsl.structs.BasicOptionDescription;
import ie.ucd.clops.dsl.structs.DSLInformation;
import ie.ucd.clops.util.StringUtil;

import org.apache.velocity.VelocityContext;

/**
 * A class to generate the documentation.
 * <BON>
 * class_chart DOCUMENT_GENERATION
 * explanation
 *   "Generation of documentation from the descriptions of options"
 * command
 *   "Generate Documentation"
 * end
 * </BON>
 */

public class DocumentGenerator extends AGenerator {

  public static final String HTML_TEMPLATE = TEMPLATE_BASE + "html.vm";
  public static final String HELP_TEMPLATE = TEMPLATE_BASE + "help.vm";



  public DocumentGenerator(DSLInformation info) throws Exception {
    super(info);
  }

}
