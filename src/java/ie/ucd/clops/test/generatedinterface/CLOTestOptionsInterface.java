package ie.ucd.clops.test.generatedinterface;

import java.util.List;
import java.io.File;

/**
 * The interface used to handle the options on the user side.
 * @author The CLOPS team
 */
public interface CLOTestOptionsInterface {


// Option Output. 
// Aliases: [-o, --output]

  /**
   * @return true if the option Output has been used
   * in the command line.
   */
  boolean isOutputSet();

  /**
   * Get the value of {@code Option} Output.
   * @return the value of the option Output if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  File getOutput();
  

// Option Compile. 
// Aliases: [-c, --compile]

  /**
   * @return true if the option Compile has been used
   * in the command line.
   */
  boolean isCompileSet();

  /**
   * Get the value of {@code Option} Compile.
   * @return the value of the option Compile if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getCompile();
  

// Option RunTests. 
// Aliases: [-r, --run]

  /**
   * @return true if the option RunTests has been used
   * in the command line.
   */
  boolean isRunTestsSet();

  /**
   * Get the value of {@code Option} RunTests.
   * @return the value of the option RunTests if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getRunTests();
  

// Option Debug. 
// Aliases: [-d, --debug]

  /**
   * @return true if the option Debug has been used
   * in the command line.
   */
  boolean isDebugSet();

  /**
   * Get the value of {@code Option} Debug.
   * @return the value of the option Debug if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getDebug();
  

// Option Input. 
// Aliases: []

  /**
   * @return true if the option Input has been used
   * in the command line.
   */
  boolean isInputSet();

  /**
   * Get the value of {@code Option} Input.
   * @return the value of the option Input if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  List<java.io.File> getInput();
  
}
