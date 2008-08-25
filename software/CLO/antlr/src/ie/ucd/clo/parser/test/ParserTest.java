package ie.ucd.clo.parser.test;

import ie.ucd.clo.parser.CLOLexer;
import ie.ucd.clo.parser.CLOParser;

import java.io.File;
import java.io.FileInputStream;
import java.io.FileNotFoundException;
import java.io.IOException;

import org.antlr.runtime.ANTLRInputStream;
import org.antlr.runtime.CommonTokenStream;
import org.antlr.runtime.RecognitionException;

public class ParserTest {

  /**
   * @param args
   */
  public static void main(String[] args) {
    if (args.length != 1) {
      System.out.println("Usage: java ie.ucd.clo.parser.test.ParserTest <filename>");
      System.exit(1);
    }

    File file = new File(args[0]);
    if (!file.exists()) {
      System.out.println("File " + args[0] + " does not exist");
    }

    try {
      CLOLexer lexer = new CLOLexer(new ANTLRInputStream(new FileInputStream(file)));
      CLOParser parser = new CLOParser(new CommonTokenStream(lexer));

      parser.prog();

      if (parser.isValidParse()) {
        System.out.println("Successfully parsed!");
      } else {
        System.out.println("Did not parse successfully.");
      }
      
    } catch (FileNotFoundException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (IOException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    } catch (RecognitionException e) {
      // TODO Auto-generated catch block
      e.printStackTrace();
    }

  }

}
