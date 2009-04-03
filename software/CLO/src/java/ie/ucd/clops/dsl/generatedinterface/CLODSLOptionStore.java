package ie.ucd.clops.dsl.generatedinterface;

import ie.ucd.clops.runtime.options.CLOPSErrorOption;
import ie.ucd.clops.runtime.options.OptionGroup;
import ie.ucd.clops.runtime.options.OptionStore;

public class CLODSLOptionStore extends OptionStore implements CLODSLOptionsInterface {

  private final ie.ucd.clops.runtime.options.FileOption outputOG;
  private final ie.ucd.clops.runtime.options.BooleanOption gen_testOG;
  private final ie.ucd.clops.runtime.options.StringOption output_packageOG;
  private final ie.ucd.clops.runtime.options.StringOption option_factoryOG;
  private final ie.ucd.clops.runtime.options.BooleanOption gen_docsOG;
  private final ie.ucd.clops.runtime.options.StringEnumOption gen_builtinOG;
  private final ie.ucd.clops.runtime.options.FileListOption gen_customOG;
  private final ie.ucd.clops.runtime.options.FileOption gen_targetOG;
  private final ie.ucd.clops.runtime.options.BooleanOption verboseOG;
  private final ie.ucd.clops.runtime.options.BooleanOption transitiveFlyRulesOG;
  private final ie.ucd.clops.runtime.options.BooleanOption InfiniteLookaheadOG;
  private final ie.ucd.clops.runtime.options.FileOption inputOG;
  private final CLOPSErrorOption CLOPSERROROPTION;

  public CLODSLOptionStore() throws ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException {

    //Options
    outputOG = new ie.ucd.clops.runtime.options.FileOption("output", "(?:-o)|(?:--output)");
    addOption(outputOG);
    outputOG.setProperty("mustExist", "true");
    outputOG.setProperty("mustbedir", "true");
    outputOG.setProperty("default", ".");
    outputOG.setProperty("description", "Output directory for generated Java files.");
    gen_testOG = new ie.ucd.clops.runtime.options.BooleanOption("gen_test", "(?:-m)|(?:--main)");
    addOption(gen_testOG);
    gen_testOG.setProperty("description", "Generate a Main class with a main method for rapid testing/debugging.");
    output_packageOG = new ie.ucd.clops.runtime.options.StringOption("output_package", "(?:-p)|(?:--package)");
    addOption(output_packageOG);
    output_packageOG.setProperty("stripquotesifpresent", "true");
    output_packageOG.setProperty("description", "Output package. If left empty the default package is used.");
    option_factoryOG = new ie.ucd.clops.runtime.options.StringOption("option_factory", "(?:-of)|(?:--option-factory)");
    addOption(option_factoryOG);
    option_factoryOG.setProperty("description", "Use this option factory instead of the default. Must be a fully qualified class name.");
    gen_docsOG = new ie.ucd.clops.runtime.options.BooleanOption("gen_docs", "(?:-d)|(?:--docs)");
    addOption(gen_docsOG);
    gen_docsOG.setProperty("description", "Use a default documentation template for generation.");
    gen_builtinOG = new ie.ucd.clops.runtime.options.StringEnumOption("gen_builtin", "(?:-b)|(?:--built-in)");
    addOption(gen_builtinOG);
    gen_builtinOG.setProperty("choices", "htmldev,html,manpage,usage,help");
    gen_builtinOG.setProperty("description", "Use a specific built-in documentation template for generation (you must specify one of the following: htmldev,html,manpage,usage).");
    gen_customOG = new ie.ucd.clops.runtime.options.FileListOption("gen_custom", "(?:-c)|(?:--custom)");
    addOption(gen_customOG);
    gen_customOG.setProperty("mustExist", "true");
    gen_customOG.setProperty("canBeDir", "false");
    gen_customOG.setProperty("description", "Use custom templates for generation.");
    gen_targetOG = new ie.ucd.clops.runtime.options.FileOption("gen_target", "(?:-t)|(?:--target)");
    addOption(gen_targetOG);
    gen_targetOG.setProperty("description", "Specify the target directory / or the target file for the generation from some templates.");
    verboseOG = new ie.ucd.clops.runtime.options.BooleanOption("verbose", "(?:-v)|(?:--verbose)");
    addOption(verboseOG);
    verboseOG.setProperty("default", "false");
    verboseOG.setProperty("description", "Print debugging messages.");
    transitiveFlyRulesOG = new ie.ucd.clops.runtime.options.BooleanOption("transitiveFlyRules", "(?:-tfr)|(?:--transitive-fly-rules)");
    addOption(transitiveFlyRulesOG);
    transitiveFlyRulesOG.setProperty("default", "false");
    transitiveFlyRulesOG.setProperty("description", "Fly rules will applied transitively.");
    InfiniteLookaheadOG = new ie.ucd.clops.runtime.options.BooleanOption("InfiniteLookahead", "(?:-oo)|(?:--infinite-lookahead)");
    addOption(InfiniteLookaheadOG);
    InfiniteLookaheadOG.setProperty("default", "false");
    InfiniteLookaheadOG.setProperty("description", "The command line parser will try harder.");
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
    final OptionGroup TemplatesOG = new OptionGroup("Templates");
    addOptionGroup(TemplatesOG);
    //Setup groupings
    all_argsOG.addOptionOrGroup(outputOG);
    all_argsOG.addOptionOrGroup(output_packageOG);
    all_argsOG.addOptionOrGroup(option_factoryOG);
    all_argsOG.addOptionOrGroup(gen_testOG);
    all_argsOG.addOptionOrGroup(verboseOG);
    all_argsOG.addOptionOrGroup(transitiveFlyRulesOG);
    all_argsOG.addOptionOrGroup(TemplatesOG);
    TemplatesOG.addOptionOrGroup(gen_docsOG);
    TemplatesOG.addOptionOrGroup(gen_builtinOG);
    TemplatesOG.addOptionOrGroup(gen_customOG);
    TemplatesOG.addOptionOrGroup(gen_targetOG);
  }
  
// Option output.
// Aliases: [-o, --output]
  
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
  
// Option gen_test.
// Aliases: [-m, --main]
  
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
  
// Option output_package.
// Aliases: [-p, --package]
  
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
  
// Option option_factory.
// Aliases: [-of, --option-factory]
  
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
  
// Option gen_docs.
// Aliases: [-d, --docs]
  
  /**
   * {@inheritDoc}
   */
  public boolean isgen_docsSet() {
    return gen_docsOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public boolean getgen_docs() {
    return gen_docsOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public boolean getRawgen_docs() {
    return gen_docsOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.BooleanOption getgen_docsOption() {
    return gen_docsOG;
  }
  
// Option gen_builtin.
// Aliases: [-b, --built-in]
  
  /**
   * {@inheritDoc}
   */
  public boolean isgen_builtinSet() {
    return gen_builtinOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public String getgen_builtin() {
    return gen_builtinOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public String getRawgen_builtin() {
    return gen_builtinOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.StringEnumOption getgen_builtinOption() {
    return gen_builtinOG;
  }
  
// Option gen_custom.
// Aliases: [-c, --custom]
  
  /**
   * {@inheritDoc}
   */
  public boolean isgen_customSet() {
    return gen_customOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public java.util.List<java.io.File> getgen_custom() {
    return gen_customOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public java.util.List<java.io.File> getRawgen_custom() {
    return gen_customOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.FileListOption getgen_customOption() {
    return gen_customOG;
  }
  
// Option gen_target.
// Aliases: [-t, --target]
  
  /**
   * {@inheritDoc}
   */
  public boolean isgen_targetSet() {
    return gen_targetOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public java.io.File getgen_target() {
    return gen_targetOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public java.io.File getRawgen_target() {
    return gen_targetOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.FileOption getgen_targetOption() {
    return gen_targetOG;
  }
  
// Option verbose.
// Aliases: [-v, --verbose]
  
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
  
// Option transitiveFlyRules.
// Aliases: [-tfr, --transitive-fly-rules]
  
  /**
   * {@inheritDoc}
   */
  public boolean istransitiveFlyRulesSet() {
    return transitiveFlyRulesOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public boolean gettransitiveFlyRules() {
    return transitiveFlyRulesOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public boolean getRawtransitiveFlyRules() {
    return transitiveFlyRulesOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.BooleanOption gettransitiveFlyRulesOption() {
    return transitiveFlyRulesOG;
  }
  
// Option InfiniteLookahead.
// Aliases: [-oo, --infinite-lookahead]
  
  /**
   * {@inheritDoc}
   */
  public boolean isInfiniteLookaheadSet() {
    return InfiniteLookaheadOG.hasValue();
  }
  
  /**
   * {@inheritDoc}
   */
  public boolean getInfiniteLookahead() {
    return InfiniteLookaheadOG.getValue();
  }

  /**
   * {@inheritDoc}
   */
  public boolean getRawInfiniteLookahead() {
    return InfiniteLookaheadOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.BooleanOption getInfiniteLookaheadOption() {
    return InfiniteLookaheadOG;
  }
  
// Option input.
// Aliases: []
  
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
