package ie.ucd.clops.codegeneration;

import ie.ucd.clops.documentation.DocumentGenerator;
import ie.ucd.clops.dsl.OptionType;
import ie.ucd.clops.dsl.structs.DSLInformation;
import ie.ucd.clops.logging.CLOLogger;
import ie.ucd.clops.runtime.options.CLOPSErrorOption;

import java.io.File;
import java.util.LinkedList;
import java.util.List;
import java.util.logging.Level;

import org.apache.velocity.VelocityContext;

/**
 * A class used to generate java code from a DSL.
 * @author Fintan
 * @author Mikolas Janota
 */
public class CodeGenerator extends DocumentGenerator {

  public CodeGenerator(DSLInformation information) throws Exception {
    super(information);
  }

  @Override
  protected VelocityContext createContext(DSLInformation information) {
    VelocityContext context = super.createContext(information);
    context.put("OptionType", CodeGenerator.class);
    context.put("CLOPSErrorOption", CLOPSErrorOption.class);
    context.put("OptionType", OptionType.class);
    context.put("CodeGenerator", CodeGenerator.class);
    return context;
  }

  /** Produces java String constant containing a given String that may contain newlines.*/
  public static List<String> quoteMultilineString(String s) {
    String[] lines = s.split("\n");
    List<String> result = new LinkedList<String>();

    for (String line : lines) {
      line = line.trim();
      if (line.equals("")) continue;
      result.add(line);
    }
    if (result.size() == 0) {
      result.add("\"\"");
    }
    return result;
  }

  private static final String TEMPLATE_BASE = "templates/";
  private static String PARSER_TEMPLATE = TEMPLATE_BASE + "gen-parser.vm";
  private static String OP_INTERFACE_TEMPLATE = TEMPLATE_BASE + "gen-interface.vm";
  private static String OP_STORE_TEMPLATE = TEMPLATE_BASE + "gen-op-store.vm";
  private static String RULE_STORE_TEMPLATE = TEMPLATE_BASE + "gen-rule-store.vm";
  private static String MAIN_TEMPLATE = TEMPLATE_BASE + "gen-main.vm";

  public static void createCode(DSLInformation dslInfo, File outputDir, boolean genTest) {
    dslInfo.processPlaceholders();
    String parserName = dslInfo.getParserName();
    try {      
      CodeGenerator codeGen = new CodeGenerator(dslInfo);
      
      File parserFile = new File(outputDir.getPath() + '/' + parserName + "Parser.java");
      codeGen.generate(parserFile, PARSER_TEMPLATE, "Code generation");
      
      File opInterfaceFile = new File(outputDir.getPath() + '/' + parserName + "OptionsInterface.java");
      codeGen.generate(opInterfaceFile, OP_INTERFACE_TEMPLATE, "Code generation");
      
      File opStoreFile = new File(outputDir.getPath() + '/' + parserName + "OptionStore.java");
      codeGen.generate(opStoreFile, OP_STORE_TEMPLATE, "Code generation");
      
      File ruleStoreFile = new File(outputDir.getPath() + '/' + parserName + "RuleStore.java");
      codeGen.generate(ruleStoreFile, RULE_STORE_TEMPLATE, "Code generation");
      
      if (genTest) {
        File mainFile = new File(outputDir.getPath() + '/' + "Main.java");
        codeGen.generate(mainFile, MAIN_TEMPLATE, "Code generation");
      }
      
    } catch (Exception e) {
      CLOLogger.getLogger().log(Level.SEVERE, "Something went wrong with code generation. " + e);
    }
  }

}
