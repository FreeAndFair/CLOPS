package ie.ucd.clops.dsl.generatedinterface;

import ie.ucd.clops.runtime.options.OptionGroup;

public class CLODSLOptionStore extends ie.ucd.clops.runtime.options.OptionStore implements CLODSLOptionsInterface {
  private final ie.ucd.clops.runtime.options.FileOption input;
  private final ie.ucd.clops.runtime.options.FileOption output;
  private final ie.ucd.clops.runtime.options.StringOption output_package;
  private final ie.ucd.clops.runtime.options.StringOption option_factory;
  public CLODSLOptionStore() throws ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException {
    input = new ie.ucd.clops.runtime.options.FileOption("input");
    input.addAlias("-i");
    input.addAlias("--input");
    input.setProperty("mustExist","true");
    input.setProperty("canbedir","false");
    addOption(input);
    output = new ie.ucd.clops.runtime.options.FileOption("output");
    output.addAlias("--output");
    output.addAlias("-o");
    output.setProperty("mustExist","true");
    output.setProperty("mustbedir","true");
    addOption(output);
    output_package = new ie.ucd.clops.runtime.options.StringOption("output_package");
    output_package.addAlias("-p");
    output_package.addAlias("--package");
    addOption(output_package);
    option_factory = new ie.ucd.clops.runtime.options.StringOption("option_factory");
    option_factory.addAlias("--option-factory");
    option_factory.addAlias("-of");
    addOption(option_factory);
    OptionGroup optional_args = new OptionGroup("optional_args");
    addOptionGroup(optional_args);
    optional_args.addOptionOrGroup(option_factory);
    optional_args.addOptionOrGroup(output_package);
    
  }
  public boolean isinputSet() {
    return input.hasValue();
    
  }
  public java.io.File getinput() {
    return input.getFileValue();
    
  }
  public boolean isoutputSet() {
    return output.hasValue();
    
  }
  public java.io.File getoutput() {
    return output.getFileValue();
    
  }
  public boolean isoutput_packageSet() {
    return output_package.hasValue();
    
  }
  public String getoutput_package() {
    return output_package.getStringValue();
    
  }
  public boolean isoption_factorySet() {
    return option_factory.hasValue();
    
  }
  public String getoption_factory() {
    return option_factory.getStringValue();
    
  }
  
}
