package ie.ucd.clops.generation;

import ie.ucd.clops.dsl.OptionType;
import ie.ucd.clops.dsl.structs.DSLInformation;
import ie.ucd.clops.logging.CLOLogger;
import ie.ucd.clops.runtime.options.CLOPSErrorOption;

import java.io.File;
import java.util.logging.Level;

import org.apache.velocity.VelocityContext;

/**
 * A class used to generate java code from a DSL.
 * @author Fintan
 * @author Mikolas Janota
 */
public class CodeGenerator extends DocumentGenerator {

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
   * @param info the informations collected by the parsing of the dsl
   * @param output the output directory for the files
   * @param genTest true if the main file has to be generated
   */
  public static void createCode(final DSLInformation info,
                                final File output, final boolean genTest) {
    info.processPlaceholders();
    try {
      CodeGenerator codeGen = new CodeGenerator(info);

      codeGen.generate(output, PARSER_TEMPLATE, "Code generation");
      codeGen.generate(output, OP_INTERFACE_TEMPLATE, "Code generation");
      codeGen.generate(output, OP_STORE_TEMPLATE, "Code generation");
      codeGen.generate(output, RULE_STORE_TEMPLATE, "Code generation");

      if (genTest) {
        codeGen.generate(output, MAIN_TEMPLATE, "Code generation");
      }

    } catch (Exception e) {
      CLOLogger.getLogger().log(Level.SEVERE,
                                "Something went wrong with code generation. "
                                + e);
    }
  }

}
