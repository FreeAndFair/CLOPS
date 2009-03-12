package ie.ucd.clops.dsl.generatedinterface;

import ie.ucd.clops.runtime.options.CLOPSErrorOption;
import ie.ucd.clops.runtime.options.OptionGroup;
import ie.ucd.clops.runtime.options.OptionStore;

public class CLODSLOptionStore extends OptionStore implements CLODSLOptionsInterface {

  private final ie.ucd.clops.runtime.options.FileOption outputOG;
  private final ie.ucd.clops.runtime.options.StringOption output_packageOG;
  private final ie.ucd.clops.runtime.options.BooleanOption gen_testOG;
  private final ie.ucd.clops.runtime.options.StringOption option_factoryOG;
  private final ie.ucd.clops.runtime.options.FileOption gen_docsOG;
  private final ie.ucd.clops.runtime.options.StringEnumOption gen_docs_builtinOG;
  private final ie.ucd.clops.runtime.options.FileOption gen_docs_customOG;
  private final ie.ucd.clops.runtime.options.BooleanOption verboseOG;
  private final ie.ucd.clops.runtime.options.FileOption inputOG;
  private final CLOPSErrorOption CLOPSERROROPTION;

  public CLODSLOptionStore() throws ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException {

    //Options
    outputOG = new ie.ucd.clops.runtime.options.FileOption("output", "(?:-o)|(?:--output)");
    addOption(outputOG);
    outputOG.setProperty("mustExist", "true");
    outputOG.setProperty("mustbedir", "true");
    outputOG.setProperty("default", ".");
    outputOG.setProperty("description", "Output directory for generated files.");
    output_packageOG = new ie.ucd.clops.runtime.options.StringOption("output_package", "(?:-p)|(?:--package)");
    addOption(output_packageOG);
    output_packageOG.setProperty("stripquotesifpresent", "true");
    output_packageOG.setProperty("description", "Output package. If left empty the default package is used.");
    gen_testOG = new ie.ucd.clops.runtime.options.BooleanOption("gen_test", "(?:-t)|(?:--test)");
    addOption(gen_testOG);
    gen_testOG.setProperty("description", "Generate a Main class with a main method for rapid testing/debugging.");
    option_factoryOG = new ie.ucd.clops.runtime.options.StringOption("option_factory", "(?:-of)|(?:--option-factory)");
    addOption(option_factoryOG);
    option_factoryOG.setProperty("description", "Use this option factory instead of the default. Must be a fully qualified class name.");
    gen_docsOG = new ie.ucd.clops.runtime.options.FileOption("gen_docs", "(?:-d)|(?:--docs)");
    addOption(gen_docsOG);
    gen_docsOG.setProperty("canBeDir", "false");
    gen_docsOG.setProperty("description", "Generate documentation and write it to the given output file.");
    gen_docs_builtinOG = new ie.ucd.clops.runtime.options.StringEnumOption("gen_docs_builtin", "(?:-b)|(?:--built-in)");
    addOption(gen_docs_builtinOG);
    gen_docs_builtinOG.setProperty("choices", "html,txt");
    gen_docs_builtinOG.setProperty("description", "Use a built-in template for documentation generation.");
    gen_docs_customOG = new ie.ucd.clops.runtime.options.FileOption("gen_docs_custom", "(?:-c)|(?:--custom)");
    addOption(gen_docs_customOG);
    gen_docs_customOG.setProperty("mustExist", "true");
    gen_docs_customOG.setProperty("canBeDir", "false");
    gen_docs_customOG.setProperty("description", "Use a custom template for documentation generation.");
    verboseOG = new ie.ucd.clops.runtime.options.BooleanOption("verbose", "(?:-v)|(?:--verbose)");
    addOption(verboseOG);
    verboseOG.setProperty("default", "false");
    verboseOG.setProperty("description", "Print debugging messages.");
    inputOG = new ie.ucd.clops.runtime.options.FileOption("input", "");
    addOption(inputOG);
    inputOG.setProperty("between", "");
    inputOG.setProperty("mustExist", "true");
    inputOG.setProperty("canbedir", "false");
    inputOG.setProperty("description", "Input file.");
  
    CLOPSERROROPTION = new ie.ucd.clops.runtime.options.CLOPSErrorOption();
    addOption(CLOPSERROROPTION);
  
    //Option groups
    final OptionGroup all_argsOG = new OptionGroup("all_args");
    addOptionGroup(all_argsOG);
    //Setup groupings
    all_argsOG.addOptionOrGroup(gen_docs_builtinOG);
    all_argsOG.addOptionOrGroup(gen_testOG);
    all_argsOG.addOptionOrGroup(gen_docs_customOG);
    all_argsOG.addOptionOrGroup(option_factoryOG);
    all_argsOG.addOptionOrGroup(verboseOG);
    all_argsOG.addOptionOrGroup(gen_docsOG);
    all_argsOG.addOptionOrGroup(outputOG);
    all_argsOG.addOptionOrGroup(output_packageOG);
  }
  
 /* Option output.
  * Description: Output directory for generated files.
  * Aliases: [-o, --output]
  */
  
  /**
   * {@inheritDoc}
   */
  public boolean isoutputSet() {
    return outputOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public java.io.File getoutput() {
    return outputOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public java.io.File getRawoutput() {
    return outputOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.FileOption getoutputOption() {
    return outputOG;
  }
  
 /* Option output_package.
  * Description: Output package. If left empty the default package is used.
  * Aliases: [-p, --package]
  */
  
  /**
   * {@inheritDoc}
   */
  public boolean isoutput_packageSet() {
    return output_packageOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public String getoutput_package() {
    return output_packageOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public String getRawoutput_package() {
    return output_packageOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.StringOption getoutput_packageOption() {
    return output_packageOG;
  }
  
 /* Option gen_test.
  * Description: Generate a Main class with a main method for rapid testing/debugging.
  * Aliases: [-t, --test]
  */
  
  /**
   * {@inheritDoc}
   */
  public boolean isgen_testSet() {
    return gen_testOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public boolean getgen_test() {
    return gen_testOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public boolean getRawgen_test() {
    return gen_testOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.BooleanOption getgen_testOption() {
    return gen_testOG;
  }
  
 /* Option option_factory.
  * Description: Use this option factory instead of the default. Must be a fully qualified class name.
  * Aliases: [-of, --option-factory]
  */
  
  /**
   * {@inheritDoc}
   */
  public boolean isoption_factorySet() {
    return option_factoryOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public String getoption_factory() {
    return option_factoryOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public String getRawoption_factory() {
    return option_factoryOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.StringOption getoption_factoryOption() {
    return option_factoryOG;
  }
  
 /* Option gen_docs.
  * Description: Generate documentation and write it to the given output file.
  * Aliases: [-d, --docs]
  */
  
  /**
   * {@inheritDoc}
   */
  public boolean isgen_docsSet() {
    return gen_docsOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public java.io.File getgen_docs() {
    return gen_docsOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public java.io.File getRawgen_docs() {
    return gen_docsOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.FileOption getgen_docsOption() {
    return gen_docsOG;
  }
  
 /* Option gen_docs_builtin.
  * Description: Use a built-in template for documentation generation.
  * Aliases: [-b, --built-in]
  */
  
  /**
   * {@inheritDoc}
   */
  public boolean isgen_docs_builtinSet() {
    return gen_docs_builtinOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public String getgen_docs_builtin() {
    return gen_docs_builtinOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public String getRawgen_docs_builtin() {
    return gen_docs_builtinOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.StringEnumOption getgen_docs_builtinOption() {
    return gen_docs_builtinOG;
  }
  
 /* Option gen_docs_custom.
  * Description: Use a custom template for documentation generation.
  * Aliases: [-c, --custom]
  */
  
  /**
   * {@inheritDoc}
   */
  public boolean isgen_docs_customSet() {
    return gen_docs_customOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public java.io.File getgen_docs_custom() {
    return gen_docs_customOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public java.io.File getRawgen_docs_custom() {
    return gen_docs_customOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.FileOption getgen_docs_customOption() {
    return gen_docs_customOG;
  }
  
 /* Option verbose.
  * Description: Print debugging messages.
  * Aliases: [-v, --verbose]
  */
  
  /**
   * {@inheritDoc}
   */
  public boolean isverboseSet() {
    return verboseOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public boolean getverbose() {
    return verboseOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public boolean getRawverbose() {
    return verboseOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.BooleanOption getverboseOption() {
    return verboseOG;
  }
  
 /* Option input.
  * Description: Input file.
  * Aliases: []
  */
  
  /**
   * {@inheritDoc}
   */
  public boolean isinputSet() {
    return inputOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public java.io.File getinput() {
    return inputOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public java.io.File getRawinput() {
    return inputOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.FileOption getinputOption() {
    return inputOG;
  }
  
}
