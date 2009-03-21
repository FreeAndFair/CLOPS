package ie.ucd.clops.dsl.generatedinterface;

/**
 * The interface used to handle the options on the user side.
 * @author The CLOPS team (kind@ucd.ie)
 */
public interface CLODSLOptionsInterface {


// Option output. 
// Aliases: [-o, --output]

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
  

// Option output_package. 
// Aliases: [-p, --package]

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
  

// Option gen_test. 
// Aliases: [-t, --test]

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
  

// Option option_factory. 
// Aliases: [-of, --option-factory]

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
  

// Option gen_docs. 
// Aliases: [-d, --docs]

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
  

// Option gen_docs_builtin. 
// Aliases: [-b, --built-in]

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
  

// Option gen_docs_custom. 
// Aliases: [-c, --custom]

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
  

// Option verbose. 
// Aliases: [-v, --verbose]

  /**
   * @return true if the option verbose has been used
   * in the command line.
   */
  boolean isverboseSet();
  
  /**
   * Get the value of {@code Option} verbose.
   * @return the value of the option verbose if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getverbose();
  

// Option transitiveFlyRules. 
// Aliases: [-tfr, --transitive-fly-rules]

  /**
   * @return true if the option transitiveFlyRules has been used
   * in the command line.
   */
  boolean istransitiveFlyRulesSet();
  
  /**
   * Get the value of {@code Option} transitiveFlyRules.
   * @return the value of the option transitiveFlyRules if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean gettransitiveFlyRules();
  

// Option input. 
// Aliases: []

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
