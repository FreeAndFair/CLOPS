package ie.ucd.clops.test.generatedinterface;

import ie.ucd.clops.runtime.options.CLOPSErrorOption;
import ie.ucd.clops.runtime.options.OptionGroup;
import ie.ucd.clops.runtime.options.OptionStore;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;
import java.util.List;
import java.io.File;
import ie.ucd.clops.runtime.options.BooleanOption;
import ie.ucd.clops.runtime.options.FileOption;
import ie.ucd.clops.runtime.options.FileListOption;

public class CLOTestOptionStore extends OptionStore implements CLOTestOptionsInterface {

  private final FileOption ogOutput;
  private final BooleanOption ogRunTests;
  private final FileListOption ogInput;
  private final CLOPSErrorOption CLOPSERROROPTION;

  public CLOTestOptionStore() throws InvalidOptionPropertyValueException {

    //Options
    ogOutput = new FileOption("Output", "(?:-o)|(?:--output)");
    addOption(ogOutput);
    ogOutput.setProperty("mustExist", "true");
    ogOutput.setProperty("mustbedir", "true");
    ogOutput.setProperty("default", ".");
    ogOutput.setProperty("aliases", "-o,--output");
    ogOutput.setProperty("description", "Output directory for generated Java files.");
    ogRunTests = new BooleanOption("RunTests", "(?:-r)|(?:--run)");
    addOption(ogRunTests);
    ogRunTests.setProperty("default", "true");
    ogRunTests.setProperty("aliases", "-r,--run");
    ogInput = new FileListOption("Input", "");
    addOption(ogInput);
    ogInput.setProperty("between", "");
    ogInput.setProperty("mustExist", "true");
    ogInput.setProperty("canbedir", "false");
    ogInput.setProperty("description", "Input testing file(s).");
  
    CLOPSERROROPTION = new ie.ucd.clops.runtime.options.CLOPSErrorOption();
    addOption(CLOPSERROROPTION);
  
    //Option groups
    final OptionGroup ogAllOptions = new OptionGroup("AllOptions");
    addOptionGroup(ogAllOptions);
    
    //Setup groupings
    //AllOptions group
    ogAllOptions.addOptionOrGroup(ogOutput);
    ogAllOptions.addOptionOrGroup(ogRunTests);
    ogAllOptions.addOptionOrGroup(ogInput);
  }
  
// Option Output.
// Aliases: [-o, --output]
  
  /**
   * {@inheritDoc}
   */
  public boolean isOutputSet() {
    return ogOutput.hasValue();
  }
  
  /** {@inheritDoc} */
  public File getOutput() {
    return ogOutput.getValue();
  }

  /** {@inheritDoc} */
  public File getRawOutput() {
    return ogOutput.getRawValue();
  }
  
  public FileOption getOutputOption() {
    return ogOutput;
  }
  
// Option RunTests.
// Aliases: [-r, --run]
  
  /**
   * {@inheritDoc}
   */
  public boolean isRunTestsSet() {
    return ogRunTests.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getRunTests() {
    return ogRunTests.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawRunTests() {
    return ogRunTests.getRawValue();
  }
  
  public BooleanOption getRunTestsOption() {
    return ogRunTests;
  }
  
// Option Input.
// Aliases: []
  
  /**
   * {@inheritDoc}
   */
  public boolean isInputSet() {
    return ogInput.hasValue();
  }
  
  /** {@inheritDoc} */
  public List<java.io.File> getInput() {
    return ogInput.getValue();
  }

  /** {@inheritDoc} */
  public List<java.io.File> getRawInput() {
    return ogInput.getRawValue();
  }
  
  public FileListOption getInputOption() {
    return ogInput;
  }
  
}
