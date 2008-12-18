
package ie.ucd.clops.dsl.generatedinterface;

import ie.ucd.clops.runtime.options.OptionGroup;

public class CLODSLOptionStore extends ie.ucd.clops.runtime.options.OptionStore implements CLODSLOptionsInterface {
  private final ie.ucd.clops.runtime.options.FileOption inputOG;
  private final ie.ucd.clops.runtime.options.FileOption outputOG;
  private final ie.ucd.clops.runtime.options.StringOption output_packageOG;
  private final ie.ucd.clops.runtime.options.BooleanOption gen_testOG;
  private final ie.ucd.clops.runtime.options.StringOption option_factoryOG;
  private final ie.ucd.clops.runtime.options.CLOPSErrorOption CLOPSERROROPTION;
  
  public CLODSLOptionStore() throws ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException {
    inputOG = new ie.ucd.clops.runtime.options.FileOption("input", "(?:-i)|(?:--input)");
    inputOG.setProperty("mustExist","true");
    inputOG.setProperty("canbedir","false");
    inputOG.setProperty("description", "input file.");
    addOption(inputOG);
    outputOG = new ie.ucd.clops.runtime.options.FileOption("output", "(?:-o)|(?:--output)");
    outputOG.setProperty("mustExist","true");
    outputOG.setProperty("mustbedir","true");
    outputOG.setProperty("description", "output file.");
    addOption(outputOG);
    output_packageOG = new ie.ucd.clops.runtime.options.StringOption("output_package", "(?:-p)|(?:--package)");
    output_packageOG.setProperty("stripquotesifpresent","true");
    output_packageOG.setProperty("description", "output package. Left empty uses the default package.");
    addOption(output_packageOG);
    gen_testOG = new ie.ucd.clops.runtime.options.BooleanOption("gen_test", "(?:-t)|(?:--test)");
    gen_testOG.setProperty("description", "generate a Main class with a main method for rapid testing/debugging.");
    addOption(gen_testOG);
    option_factoryOG = new ie.ucd.clops.runtime.options.StringOption("option_factory", "(?:-of)|(?:--option-factory)");
    option_factoryOG.setProperty("description", "use this option factory instead of the default. Must be a fully qualified class name.");
    addOption(option_factoryOG);
    CLOPSERROROPTION = new ie.ucd.clops.runtime.options.CLOPSErrorOption();
    addOption(CLOPSERROROPTION);
    OptionGroup optional_argsOG = new OptionGroup("optional_args");
    addOptionGroup(optional_argsOG);
    optional_argsOG.addOptionOrGroup(gen_testOG);
    optional_argsOG.addOptionOrGroup(option_factoryOG);
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
  
}
