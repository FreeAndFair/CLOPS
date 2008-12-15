package ie.ucd.clops.dsl.generatedinterface;

import ie.ucd.clops.runtime.options.OptionGroup;

public class CLODSLOptionStore extends ie.ucd.clops.runtime.options.OptionStore implements CLODSLOptionsInterface {
  private final ie.ucd.clops.runtime.options.FileOption input;
  private final ie.ucd.clops.runtime.options.FileOption output;
  private final ie.ucd.clops.runtime.options.StringOption output_package;
  private final ie.ucd.clops.runtime.options.BooleanOption gen_test;
  private final ie.ucd.clops.runtime.options.StringOption option_factory;
  public CLODSLOptionStore() throws ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException {
    input = new ie.ucd.clops.runtime.options.FileOption("input", "(?:-i)|(?:--input)");
    input.setProperty("mustExist","true");
    input.setProperty("canbedir","false");
    addOption(input);
    output = new ie.ucd.clops.runtime.options.FileOption("output", "(?:-o)|(?:--output)");
    output.setProperty("mustExist","true");
    output.setProperty("mustbedir","true");
    addOption(output);
    output_package = new ie.ucd.clops.runtime.options.StringOption("output_package", "(?:-p)|(?:--package)");
    output_package.setProperty("stripquotesifpresent","true");
    addOption(output_package);
    gen_test = new ie.ucd.clops.runtime.options.BooleanOption("gen_test", "(?:-t)|(?:--test)");
    addOption(gen_test);
    option_factory = new ie.ucd.clops.runtime.options.StringOption("option_factory", "(?:-of)|(?:--option-factory)");
    addOption(option_factory);
    OptionGroup optional_args = new OptionGroup("optional_args");
    addOptionGroup(optional_args);
    optional_args.addOptionOrGroup(gen_test);
    optional_args.addOptionOrGroup(option_factory);
    optional_args.addOptionOrGroup(output_package);
    
  }
  public boolean isinputSet() {
    return input.hasValue();
    
  }
  public java.io.File getinput() {
    return input.getValue();
    
  }
  public ie.ucd.clops.runtime.options.FileOption getinputOption() {
    return input;
    
  }
  public boolean isoutputSet() {
    return output.hasValue();
    
  }
  public java.io.File getoutput() {
    return output.getValue();
    
  }
  public ie.ucd.clops.runtime.options.FileOption getoutputOption() {
    return output;
    
  }
  public boolean isoutput_packageSet() {
    return output_package.hasValue();
    
  }
  public String getoutput_package() {
    return output_package.getValue();
    
  }
  public ie.ucd.clops.runtime.options.StringOption getoutput_packageOption() {
    return output_package;
    
  }
  public boolean isgen_testSet() {
    return gen_test.hasValue();
    
  }
  public boolean getgen_test() {
    return gen_test.getValue();
    
  }
  public ie.ucd.clops.runtime.options.BooleanOption getgen_testOption() {
    return gen_test;
    
  }
  public boolean isoption_factorySet() {
    return option_factory.hasValue();
    
  }
  public String getoption_factory() {
    return option_factory.getValue();
    
  }
  public ie.ucd.clops.runtime.options.StringOption getoption_factoryOption() {
    return option_factory;
    
  }
  
}
