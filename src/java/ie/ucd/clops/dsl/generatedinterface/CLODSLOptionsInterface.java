package ie.ucd.clops.dsl.generatedinterface;

import java.util.List;
import java.io.File;

/**
 * The interface used to handle the options on the user side.
 * @author The CLOPS team
 */
public interface CLODSLOptionsInterface {


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
  

// Option Test. 
// Aliases: [-m, --main]

  /**
   * @return true if the option Test has been used
   * in the command line.
   */
  boolean isTestSet();

  /**
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

  /**
   * Get the value of {@code Option} OutputPackage.
   * @return the value of the option OutputPackage if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  String getOutputPackage();
  

// Option Docs. 
// Aliases: [-d, --docs]

  /**
   * @return true if the option Docs has been used
   * in the command line.
   */
  boolean isDocsSet();

  /**
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

  /**
   * The enumeration type used to represent the string enum option.
   */
  static enum  Builtin {
    htmldev("htmldev"),    html("html"),    manpage("manpage"),    usage("usage"),    help("help");

    private final String[] matchStrings;
    private Builtin(final String... s) {
      matchStrings = s;
    }
    public String toString() {
      return matchStrings.toString();
    }
    /**
     * Returns the appropriate enum value for the given string
     * @param s one of the following strings: [htmldev, html, manpage, usage, help]
     * @return a valid Builtin member.
     */
    public static Builtin get(final String s) {
      for (Builtin value : Builtin.values()) {
        for (String m : value.matchStrings) {
          if (m.equalsIgnoreCase(s)) return value;
        }
      }
      return null;
    }
    
    public static List<Builtin> get(final List<String> ss) {
      List<Builtin> res = new java.util.ArrayList<Builtin>(ss.size());
      for (String s : ss) {
        res.add(get(s));
      }
      return res;
    }
    
  }

  /**
   * Get the value of {@code Option} Builtin.
   * @return the value of the option Builtin if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  List<Builtin> getBuiltin();
  

// Option Custom. 
// Aliases: [-c, --custom]

  /**
   * @return true if the option Custom has been used
   * in the command line.
   */
  boolean isCustomSet();

  /**
   * Get the value of {@code Option} Custom.
   * @return the value of the option Custom if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  List<java.io.File> getCustom();
  

// Option Target. 
// Aliases: [-t, --target]

  /**
   * @return true if the option Target has been used
   * in the command line.
   */
  boolean isTargetSet();

  /**
   * Get the value of {@code Option} Target.
   * @return the value of the option Target if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  File getTarget();
  

// Option StaticCheck. 
// Aliases: [-sc, --static-check]

  /**
   * @return true if the option StaticCheck has been used
   * in the command line.
   */
  boolean isStaticCheckSet();

  /**
   * Get the value of {@code Option} StaticCheck.
   * @return the value of the option StaticCheck if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getStaticCheck();
  

// Option Verbose. 
// Aliases: [-v, --verbose]

  /**
   * @return true if the option Verbose has been used
   * in the command line.
   */
  boolean isVerboseSet();

  /**
   * Get the value of {@code Option} Verbose.
   * @return the value of the option Verbose if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getVerbose();
  

// Option Quiet. 
// Aliases: [-q, --quiet]

  /**
   * @return true if the option Quiet has been used
   * in the command line.
   */
  boolean isQuietSet();

  /**
   * Get the value of {@code Option} Quiet.
   * @return the value of the option Quiet if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getQuiet();
  

// Option Version. 
// Aliases: [-version]

  /**
   * @return true if the option Version has been used
   * in the command line.
   */
  boolean isVersionSet();

  /**
   * Get the value of {@code Option} Version.
   * @return the value of the option Version if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getVersion();
  

// Option OptionFactory. 
// Aliases: [-of, --option-factory]

  /**
   * @return true if the option OptionFactory has been used
   * in the command line.
   */
  boolean isOptionFactorySet();

  /**
   * Get the value of {@code Option} OptionFactory.
   * @return the value of the option OptionFactory if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  String getOptionFactory();
  

// Option TransitiveFlyRules. 
// Aliases: [-tfr, --transitive-fly-rules]

  /**
   * @return true if the option TransitiveFlyRules has been used
   * in the command line.
   */
  boolean isTransitiveFlyRulesSet();

  /**
   * Get the value of {@code Option} TransitiveFlyRules.
   * @return the value of the option TransitiveFlyRules if it has been set
   * using the arguments. Throws an {@code IllegalStateException} otherwise.
   */ 
  boolean getTransitiveFlyRules();
  

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
  File getInput();
  
}
