package ie.ucd.clops;

import ie.ucd.clops.util.FileUtil;

import java.io.IOException;

public class Version {

  private static String version = null;
  
  /**
   * Get the version of clops that is running.
   * @return a string containing the version number and build date of clops.
   */
  public static String getVersion() {
    if (version == null) {
      try {
        version = FileUtil.readToString("version");
      } catch (IOException ioe) {
        version = "An error occurred when reading the version.";
      }
    }
    return version;
  }
  
}
