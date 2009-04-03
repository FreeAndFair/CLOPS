package ie.ucd.clops.generation;

import java.io.File;
import java.util.HashMap;
import java.util.List;

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

  /** Explanation for the error message: "Document generation". */
  public static final String EXPLANATION = "Document generation";
  public static String keys [] = {"htmldev", "html", "manpage", "usage", "help"};
  private final HashMap<String, String> templateLib = new HashMap<String, String>();;

  /**
   * Creates a document generator from the collected informations.
   * @param info the infos from the DSL
   * @throws Exception in case the initialisation of Velocity fails
   */
  public DocumentGenerator(final DSLInformation info) throws Exception {
    super(info);
    init();
  }


  private void init() {
    templateLib.put("htmldev", TEMPLATE_BASE + "htmldev.vm");
    templateLib.put("html", TEMPLATE_BASE + "html.vm");
    templateLib.put("manpage", TEMPLATE_BASE + "manpage.vm");
    templateLib.put("usage", TEMPLATE_BASE + "usage.vm");
    templateLib.put("help", TEMPLATE_BASE + "help.vm");
  }


  public void generateDefault(File output) {
    generate(output, templateLib.get("html"), EXPLANATION);
    
  }

  public void generateBuiltin(File output, String builtin) {
    generate(output, templateLib.get(builtin.toLowerCase()), EXPLANATION);
  }


  public void generateCustom(File output, List<File> customz) {
    for (File f: customz) {
      generate(output, f.getAbsolutePath(), EXPLANATION);
    }
    
  }

}
