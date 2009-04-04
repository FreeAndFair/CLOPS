package ie.ucd.clops.dsl.generatedinterface;

/**
 * The interface used to handle the options on the user side.
 * @author The CLOPS team (kind@ucd.ie)
 */
public interface CLODSLOptionsInterface {


// Option Output. 
// Aliases: [-o, --output]

  /**
   * @return true if the option Output has been used
   * in the command line.
   */
  boolean isOutputSet();
  
  
  
      /** file
   * Get the value of {@code Option} Output.
   * @return the value of the option Output if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  java.io.File getOutput();
  

// Option Test. 
// Aliases: [-m, --main]

  /**
   * @return true if the option Test has been used
   * in the command line.
   */
  boolean isTestSet();
  
  
  
      /** boolean
   * Get the value of {@code Option} Test.
   * @return the value of the option Test if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getTest();
  

// Option OutputPackage. 
// Aliases: [-p, --package]

  /**
   * @return true if the option OutputPackage has been used
   * in the command line.
   */
  boolean isOutputPackageSet();
  
  
  
      /** string
   * Get the value of {@code Option} OutputPackage.
   * @return the value of the option OutputPackage if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  String getOutputPackage();
  

// Option OptionFactory. 
// Aliases: [-of, --option-factory]

  /**
   * @return true if the option OptionFactory has been used
   * in the command line.
   */
  boolean isOptionFactorySet();
  
  
  
      /** string
   * Get the value of {@code Option} OptionFactory.
   * @return the value of the option OptionFactory if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  String getOptionFactory();
  

// Option Docs. 
// Aliases: [-d, --docs]

  /**
   * @return true if the option Docs has been used
   * in the command line.
   */
  boolean isDocsSet();
  
  
  
      /** boolean
   * Get the value of {@code Option} Docs.
   * @return the value of the option Docs if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getDocs();
  

// Option Builtin. 
// Aliases: [-b, --built-in]

  /**
   * @return true if the option Builtin has been used
   * in the command line.
   */
  boolean isBuiltinSet();
  
  
  
    enum  Builtin {
  htmldev,html,manpage,usage,help;
  public static Builtin get(String s) {
	     	       if (htmldev.toString().equals(s)) {
	         return htmldev;
	       }
	     	       if (html.toString().equals(s)) {
	         return html;
	       }
	     	       if (manpage.toString().equals(s)) {
	         return manpage;
	       }
	     	       if (usage.toString().equals(s)) {
	         return usage;
	       }
	     	       if (help.toString().equals(s)) {
	         return help;
	       }
	     	     return null;
	   }
	}
	
    /** string-enum
   * Get the value of {@code Option} Builtin.
   * @return the value of the option Builtin if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  Builtin getBuiltin();
  

// Option Custom. 
// Aliases: [-c, --custom]

  /**
   * @return true if the option Custom has been used
   * in the command line.
   */
  boolean isCustomSet();
  
  
  
      /** file-list
   * Get the value of {@code Option} Custom.
   * @return the value of the option Custom if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  java.util.List<java.io.File> getCustom();
  

// Option Target. 
// Aliases: [-t, --target]

  /**
   * @return true if the option Target has been used
   * in the command line.
   */
  boolean isTargetSet();
  
  
  
      /** file
   * Get the value of {@code Option} Target.
   * @return the value of the option Target if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  java.io.File getTarget();
  

// Option Verbose. 
// Aliases: [-v, --verbose]

  /**
   * @return true if the option Verbose has been used
   * in the command line.
   */
  boolean isVerboseSet();
  
  
  
      /** boolean
   * Get the value of {@code Option} Verbose.
   * @return the value of the option Verbose if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getVerbose();
  

// Option TransitiveFlyRules. 
// Aliases: [-tfr, --transitive-fly-rules]

  /**
   * @return true if the option TransitiveFlyRules has been used
   * in the command line.
   */
  boolean isTransitiveFlyRulesSet();
  
  
  
      /** boolean
   * Get the value of {@code Option} TransitiveFlyRules.
   * @return the value of the option TransitiveFlyRules if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getTransitiveFlyRules();
  

// Option InfiniteLookahead. 
// Aliases: [-oo, --infinite-lookahead]

  /**
   * @return true if the option InfiniteLookahead has been used
   * in the command line.
   */
  boolean isInfiniteLookaheadSet();
  
  
  
      /** boolean
   * Get the value of {@code Option} InfiniteLookahead.
   * @return the value of the option InfiniteLookahead if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getInfiniteLookahead();
  

// Option Input. 
// Aliases: []

  /**
   * @return true if the option Input has been used
   * in the command line.
   */
  boolean isInputSet();
  
  
  
      /** file
   * Get the value of {@code Option} Input.
   * @return the value of the option Input if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  java.io.File getInput();
  
}
