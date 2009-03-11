package ie.ucd.clops.dsl.generatedinterface;

/**
 * The interface used to handle the options on the user side.
 * @author The CLOPS team (kind@ucd.ie)
 */
public interface CLODSLOptionsInterface {


 /* Option output.
  * Description: Output directory for generated files.
  * Aliases: [-o, --output]
  */

  /**
   * @return true if the option output has been used
   * in the command line.
   */
  boolean isoutputSet();
  
  /**
   * Get the value of {@code Option} output.
   * @return the value of the option output if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  java.io.File getoutput();
  

 /* Option output_package.
  * Description: Output package. If left empty the default package is used.
  * Aliases: [-p, --package]
  */

  /**
   * @return true if the option output_package has been used
   * in the command line.
   */
  boolean isoutput_packageSet();
  
  /**
   * Get the value of {@code Option} output_package.
   * @return the value of the option output_package if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  String getoutput_package();
  

 /* Option gen_test.
  * Description: Generate a Main class with a main method for rapid testing/debugging.
  * Aliases: [-t, --test]
  */

  /**
   * @return true if the option gen_test has been used
   * in the command line.
   */
  boolean isgen_testSet();
  
  /**
   * Get the value of {@code Option} gen_test.
   * @return the value of the option gen_test if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getgen_test();
  

 /* Option option_factory.
  * Description: Use this option factory instead of the default. Must be a fully qualified class name.
  * Aliases: [-of, --option-factory]
  */

  /**
   * @return true if the option option_factory has been used
   * in the command line.
   */
  boolean isoption_factorySet();
  
  /**
   * Get the value of {@code Option} option_factory.
   * @return the value of the option option_factory if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  String getoption_factory();
  

 /* Option gen_docs.
  * Description: Generate documentation and write it to the given output file.
  * Aliases: [-d, --docs]
  */

  /**
   * @return true if the option gen_docs has been used
   * in the command line.
   */
  boolean isgen_docsSet();
  
  /**
   * Get the value of {@code Option} gen_docs.
   * @return the value of the option gen_docs if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  java.io.File getgen_docs();
  

 /* Option gen_docs_builtin.
  * Description: Use a built-in template for documentation generation.
  * Aliases: [-b, --built-in]
  */

  /**
   * @return true if the option gen_docs_builtin has been used
   * in the command line.
   */
  boolean isgen_docs_builtinSet();
  
  /**
   * Get the value of {@code Option} gen_docs_builtin.
   * @return the value of the option gen_docs_builtin if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  String getgen_docs_builtin();
  

 /* Option gen_docs_custom.
  * Description: Use a custom template for documentation generation.
  * Aliases: [-c, --custom]
  */

  /**
   * @return true if the option gen_docs_custom has been used
   * in the command line.
   */
  boolean isgen_docs_customSet();
  
  /**
   * Get the value of {@code Option} gen_docs_custom.
   * @return the value of the option gen_docs_custom if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  java.io.File getgen_docs_custom();
  

 /* Option input.
  * Description: Input file.
  * Aliases: []
  */

  /**
   * @return true if the option input has been used
   * in the command line.
   */
  boolean isinputSet();
  
  /**
   * Get the value of {@code Option} input.
   * @return the value of the option input if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  java.io.File getinput();
  
}
