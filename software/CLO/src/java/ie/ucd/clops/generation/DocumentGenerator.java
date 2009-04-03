package ie.ucd.clops.generation;

import ie.ucd.clops.dsl.structs.DSLInformation;

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

  /** the template to generate the html help: templates/html.vm. */
  public static final String HTML_TEMPLATE = TEMPLATE_BASE + "html.vm";
  /** the template to generate the manpage: templates/help.vm. */
  public static final String HELP_TEMPLATE = TEMPLATE_BASE + "help.vm";


  /**
   * Creates a document generator from the collected informations.
   * @param info the infos from the DSL
   * @throws Exception in case the initialisation of Velocity fails
   */
  public DocumentGenerator(final DSLInformation info) throws Exception {
    super(info);
  }

}
