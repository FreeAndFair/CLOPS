package ie.ucd.clops.dsl.parser;

import ie.ucd.clops.codegeneration.CodeGenerator;
import ie.ucd.clops.dsl.structs.OptionDescription;
import ie.ucd.clops.dsl.structs.OptionGroupDescription;
import ie.ucd.clops.dsl.structs.OverrideRuleDescription;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;
import java.util.Collection;

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

public class ParserTest {

  /**
   * @param args
   */
  public static void main(String[] args) {
    if (args.length != 2) {
      System.out.println("Usage: java ie.ucd.clo.parser.test.ParserTest <filename> <outputdir>");
      System.exit(1);
    }

    File file = new File(args[0]);
    if (!file.exists()) {
      System.out.println("File " + args[0] + " does not exist");
    }
    
    File outputDir = new File(args[1]);
    if (!outputDir.exists() || !outputDir.isDirectory()) {
      System.out.println("Output directory " + args[1] + " does not exist");
    }

    CLOParser parser = null;
    try {
      CLOLexer lexer = new CLOLexer(new ANTLRInputStream(new FileInputStream(file)));
      parser = new CLOParser(new CommonTokenStream(lexer));

      parser.prog();

      if (parser.isValidParse()) {
        System.out.println("Successfully parsed dsl file!");
        
        Collection<OptionDescription> optionDescriptions = parser.getOptionDescriptions();
        Collection<OptionGroupDescription> optionGroupDescriptions = parser.getOptionGroupDescriptions();
        Collection<OverrideRuleDescription> overrideRuleDescriptions = parser.getOverrideRuleDescriptions();
        String formatString = parser.getFormatString();
        
        formatString = formatString.replaceAll("\\n", "");
        CodeGenerator.createCode(formatString, optionDescriptions, optionGroupDescriptions, overrideRuleDescriptions, outputDir);
        System.out.println("Created code in " + outputDir.getAbsolutePath());
        
      } else {
        System.out.println("Did not parse successfully.");
        if (parser.getCustomErrorMessage() != null) {
          System.err.println(parser.getCustomErrorMessage());
        }
      }
      
    } catch (FileNotFoundException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (IOException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (RecognitionException e) {
      System.out.println("Caught recognition error");
      if (parser.getCustomErrorMessage() != null) {
        System.err.println(parser.getCustomErrorMessage());
      }
      // TODO Auto-generated catch block
      e.printStackTrace();
    } 

  }

}
