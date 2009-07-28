/**
 * Copyright (c) 2007-2009, Fintan Fairmichael, University College Dublin under the BSD licence.
 * See LICENCE.TXT for details.
 */
package ie.ucd.clops.util;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.List;

/**
 * A class to allow reading specific lines from source files.
 * @author Fintan
 *
 */
public class SourceLineReader {

  private final BufferedReader br;
  private final List<String> lines;
  private int lineReadTo;

  /**
   * Creates a SourceLineReader to read from the given File.
   * @param sourceFile The File to read from.
   */
  public SourceLineReader(File sourceFile) {
    BufferedReader tempBr;
    try {
      tempBr = new BufferedReader(new FileReader(sourceFile));
    } catch (FileNotFoundException ioe) {
      tempBr = null;
    }
    this.br = tempBr;
    lines = new ArrayList<String>();
    lineReadTo = 0;
  }
  
  public SourceLineReader(List<String> lines) {
    this.lines = lines;
    this.br = null;
    this.lineReadTo = lines.size();
  }

  /**
   * Gets the line requested from the source file. If the source file does not exist, 
   * if there is a problem reading from the file, or if the line asked for is past the end
   * of the file, then null will be returned.
   * @param lineNumber
   * @return
   */
  public String getLine(int lineNumber) {
    if (lineNumber < 1) {
      return "<INVALID LINE>";
    }
    if (lineReadTo >= lineNumber) {
      return lines.get(lineNumber-1);
    } else {
      try {
        readUpTo(lineNumber);
        return lines.get(lineNumber-1);
      } catch (IOException ioe) {
        System.err.println("Error encountered whilst trying to read from the source file:");
        System.err.println("\t" + ioe);
        return null;
      }
    }
  }

  /**
   * Instructs the SourceLinereader to ensure that everything up to the line indicated
   * has been read and is held in memory.
   * @param lineToReadTo The line to read up to.
   * @throws IOException If there is a problem reading from the source file.
   */
  private void readUpTo(final int lineToReadTo) throws IOException {
    if (lineToReadTo <= lineReadTo) {
      return;
    }
    
    if (br == null) {
      throw new IOException("The source file was not found or not set.");
    } 

    for ( ; lineReadTo < lineToReadTo; lineReadTo++) {
      String line = br.readLine();
      if (line == null) {
        //TODO a new Exception type for here, so we can identify exactly what's happened!
        throw new IOException("Attempted to read line " + lineReadTo + ", but the file is not that long.");
      } else {
        lines.add(line);
      }
    }
  }
  
  
  //TODO this is _not_ a very efficient way of doing this.
  //Perhaps store a corresponding list with cumulative character absolutes?
//  public int getCharOffset(int lineNumber) throws IOException {
//    readUpTo(lineNumber);
//    int count = 0;
//    for (int i=0; i < lineNumber-1; i++) {
//      count += lines.get(i).length() + 1;
//    }
//    return count;
//  }

}
