import java.io.File;
import generated.WcParser;
import generated.WcOptionsInterface;
import ie.ucd.clops.runtime.errors.ParseResult;

public class Main {
  public static void main(String[] args)  {
    WcParser parser = new WcParser();
    ParseResult argsParseResult = parser.parse(args);
    if (!argsParseResult.successfulParse()) {
       argsParseResult.printErrorsAndWarnings(System.err);
       System.out.println("Usage: java Main [OPTIONS] file...");
       System.exit(1);
    }
    WcOptionsInterface opt = parser.getOptionStore();
    if (opt.isWordsSet()) System.out.println("I should print a word count.");
    if (opt.isBytesSet()) System.out.println("I should print a byte count.");
    for (File f : opt.getFiles()) checkFile(f);
    for (File f : opt.getDashFiles()) checkFile(f);
  }

  public static void checkFile(File f) {
    System.out.print("The file " + f.getPath());
    if (f.exists())
      System.out.println(" exists.");
    else
      System.out.println(" does not exist.");
  }
}

