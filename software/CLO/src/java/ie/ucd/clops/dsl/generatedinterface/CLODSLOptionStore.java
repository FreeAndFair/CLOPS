package ie.ucd.clops.dsl.generatedinterface;

import ie.ucd.clops.runtime.options.*;

public class CLODSLOptionStore extends OptionStore implements CLODSLOptionsInterface {

  private final ie.ucd.clops.runtime.options.FileOption inputOG;
  private final ie.ucd.clops.runtime.options.FileOption outputOG;
  private final ie.ucd.clops.runtime.options.StringOption output_packageOG;
  private final ie.ucd.clops.runtime.options.BooleanOption gen_testOG;
  private final ie.ucd.clops.runtime.options.StringOption option_factoryOG;
  private final ie.ucd.clops.runtime.options.FileOption gen_docsOG;
  private final ie.ucd.clops.runtime.options.StringEnumOption gen_docs_builtinOG;
  private final ie.ucd.clops.runtime.options.FileOption gen_docs_customOG;
  private final CLOPSErrorOption CLOPSERROROPTION;

  public CLODSLOptionStore() throws ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException {

    //Options
    inputOG = new ie.ucd.clops.runtime.options.FileOption("input","(?:-i)|(?:--input)");
    addOption(inputOG);
    inputOG.setProperty("mustExist","true");
    inputOG.setProperty("canbedir","false");
    inputOG.setProperty("description", "Input file.");
    outputOG = new ie.ucd.clops.runtime.options.FileOption("output","(?:-o)|(?:--output)");
    addOption(outputOG);
    outputOG.setProperty("mustExist","true");
    outputOG.setProperty("mustbedir","true");
    outputOG.setProperty("description", "Output directory for generated files.");
    output_packageOG = new ie.ucd.clops.runtime.options.StringOption("output_package","(?:-p)|(?:--package)");
    addOption(output_packageOG);
    output_packageOG.setProperty("stripquotesifpresent","true");
    output_packageOG.setProperty("description", "Output package. Left empty uses the default package.");
    gen_testOG = new ie.ucd.clops.runtime.options.BooleanOption("gen_test","(?:-t)|(?:--test)");
    addOption(gen_testOG);
    gen_testOG.setProperty("description", "Generate a Main class with a main method for rapid testing/debugging.");
    option_factoryOG = new ie.ucd.clops.runtime.options.StringOption("option_factory","(?:-of)|(?:--option-factory)");
    addOption(option_factoryOG);
    option_factoryOG.setProperty("description", "Use this option factory instead of the default. Must be a fully qualified class name.");
    gen_docsOG = new ie.ucd.clops.runtime.options.FileOption("gen_docs","(?:-d)|(?:--docs)");
    addOption(gen_docsOG);
    gen_docsOG.setProperty("canBeDir","false");
    gen_docsOG.setProperty("description", "Generate documentation and write it to the given output file.");
    gen_docs_builtinOG = new ie.ucd.clops.runtime.options.StringEnumOption("gen_docs_builtin","(?:-b)|(?:--built-in)");
    addOption(gen_docs_builtinOG);
    gen_docs_builtinOG.setProperty("choices","html,txt");
    gen_docs_builtinOG.setProperty("description", "Use a built-in template for documentation generation.");
    gen_docs_customOG = new ie.ucd.clops.runtime.options.FileOption("gen_docs_custom","(?:-c)|(?:--custom)");
    addOption(gen_docs_customOG);
    gen_docs_customOG.setProperty("mustExist","true");
    gen_docs_customOG.setProperty("canBeDir","false");
    gen_docs_customOG.setProperty("description", "Use a custom template for documentation generation.");
  
    CLOPSERROROPTION = new ie.ucd.clops.runtime.options.CLOPSErrorOption();
    addOption(CLOPSERROROPTION);
  
    //Option groups
    OptionGroup all_argsOG = new OptionGroup("all_args");
    addOptionGroup(all_argsOG);
    OptionGroup required_argsOG = new OptionGroup("required_args");
    addOptionGroup(required_argsOG);
    OptionGroup optional_argsOG = new OptionGroup("optional_args");
    addOptionGroup(optional_argsOG);
    //Setup groupings
    all_argsOG.addOptionOrGroup(optional_argsOG);
    all_argsOG.addOptionOrGroup(required_argsOG);
    required_argsOG.addOptionOrGroup(inputOG);
    required_argsOG.addOptionOrGroup(outputOG);
    optional_argsOG.addOptionOrGroup(gen_docs_builtinOG);
    optional_argsOG.addOptionOrGroup(gen_testOG);
    optional_argsOG.addOptionOrGroup(gen_docs_customOG);
    optional_argsOG.addOptionOrGroup(option_factoryOG);
    optional_argsOG.addOptionOrGroup(gen_docsOG);
    optional_argsOG.addOptionOrGroup(output_packageOG);
  }
  
  public boolean isinputSet() {
    return inputOG.hasValue();
  }
  
  public java.io.File getinput() {
    return inputOG.getValue();
  }
  
  public ie.ucd.clops.runtime.options.FileOption getinputOption() {
    return inputOG;
  }
  public boolean isoutputSet() {
    return outputOG.hasValue();
  }
  
  public java.io.File getoutput() {
    return outputOG.getValue();
  }
  
  public ie.ucd.clops.runtime.options.FileOption getoutputOption() {
    return outputOG;
  }
  public boolean isoutput_packageSet() {
    return output_packageOG.hasValue();
  }
  
  public String getoutput_package() {
    return output_packageOG.getValue();
  }
  
  public ie.ucd.clops.runtime.options.StringOption getoutput_packageOption() {
    return output_packageOG;
  }
  public boolean isgen_testSet() {
    return gen_testOG.hasValue();
  }
  
  public boolean getgen_test() {
    return gen_testOG.getValue();
  }
  
  public ie.ucd.clops.runtime.options.BooleanOption getgen_testOption() {
    return gen_testOG;
  }
  public boolean isoption_factorySet() {
    return option_factoryOG.hasValue();
  }
  
  public String getoption_factory() {
    return option_factoryOG.getValue();
  }
  
  public ie.ucd.clops.runtime.options.StringOption getoption_factoryOption() {
    return option_factoryOG;
  }
  public boolean isgen_docsSet() {
    return gen_docsOG.hasValue();
  }
  
  public java.io.File getgen_docs() {
    return gen_docsOG.getValue();
  }
  
  public ie.ucd.clops.runtime.options.FileOption getgen_docsOption() {
    return gen_docsOG;
  }
  public boolean isgen_docs_builtinSet() {
    return gen_docs_builtinOG.hasValue();
  }
  
  public String getgen_docs_builtin() {
    return gen_docs_builtinOG.getValue();
  }
  
  public ie.ucd.clops.runtime.options.StringEnumOption getgen_docs_builtinOption() {
    return gen_docs_builtinOG;
  }
  public boolean isgen_docs_customSet() {
    return gen_docs_customOG.hasValue();
  }
  
  public java.io.File getgen_docs_custom() {
    return gen_docs_customOG.getValue();
  }
  
  public ie.ucd.clops.runtime.options.FileOption getgen_docs_customOption() {
    return gen_docs_customOG;
  }
}