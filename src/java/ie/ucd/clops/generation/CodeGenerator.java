package ie.ucd.clops.generation;

import ie.ucd.clops.dsl.structs.DSLInformation;

import java.io.File;

/**
 * A class used to generate java code from a DSL.
 * @author Fintan
 * @author Mikolas Janota
 */
public class CodeGenerator extends DocumentGenerator {

  // TODO(rgrig): These string concatenations look like asking for trouble.
  /** the template to generate the parser: templates/gen-parser.vm. */
  private static final String PARSER_TEMPLATE =
    TEMPLATE_BASE + "gen-parser.vm";
  /** the template to generate the interface: templates/gen-interface.vm. */
  private static final String OP_INTERFACE_TEMPLATE =
    TEMPLATE_BASE + "gen-interface.vm";
  /** the template to generate the option store: templates/gen-op-store.vm. */
  private static final String OP_STORE_TEMPLATE =
    TEMPLATE_BASE + "gen-op-store.vm";
  /** the template to generate the rules store: templates/gen-rule-store.vm. */
  private static final String RULE_STORE_TEMPLATE =
    TEMPLATE_BASE + "gen-rule-store.vm";
  /** the template to generate the main: templates/gen-main.vm. */
  private static final String MAIN_TEMPLATE =
    TEMPLATE_BASE + "gen-main.vm";
  private static final String ANT_TEMPLATE =
    TEMPLATE_BASE + "gen-ant-task.vm";

  /**
   * Creates a code generator from the collected informations.
   * @param info the infos from the DSL
   * @throws Exception in case the initialisation of Velocity fails
   */
  public CodeGenerator(final DSLInformation info) throws Exception {
    super(info);
  }


  /**
   * Creates the codes for the option parser using the templates.
   * @param output the output directory for the files
   * @param genTest true if the main file has to be generated
   */
  public void createCode(final File output, final boolean genTest) {
    final CodeGenerator codeGen = this;

    codeGen.generate(output, PARSER_TEMPLATE, "Code generation");
    codeGen.generate(output, OP_INTERFACE_TEMPLATE, "Code generation");
    codeGen.generate(output, OP_STORE_TEMPLATE, "Code generation");
    codeGen.generate(output, RULE_STORE_TEMPLATE, "Code generation");
    //codeGen.generate(output, ANT_TEMPLATE, "Code generation");

    if (genTest) {
      codeGen.generate(output, MAIN_TEMPLATE, "Code generation");
    }
  }

}
