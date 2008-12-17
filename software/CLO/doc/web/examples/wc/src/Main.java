import java.io.File;
import generated.WcParser;
import generated.WcOptionsInterface;

public class Main {
  public static void main(String[] args) throws Exception {
    WcParser parser = new WcParser();
    if (!parser.parse(args)) {
      System.out.println("Usage: java Main [OPTIONS] file...");
      System.exit(1);
    }
    WcOptionsInterface opt = parser.getOptionStore();
    if (opt.isWordsSet())
      System.out.println("I should print a word count.");
    if (opt.isBytesSet())
      System.out.println("I should print a byte count.");
    if (opt.isFilesSet()) {
      for (File f : opt.getFiles()) {
        System.out.print("The file " + f.getAbsolutePath());
        if (f.exists())
          System.out.println(" exists.");
        else
          System.out.println(" does not exist.");
      }
    }
  }
}

