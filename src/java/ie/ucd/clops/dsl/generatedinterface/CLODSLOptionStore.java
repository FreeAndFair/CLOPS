package ie.ucd.clops.dsl.generatedinterface;

import ie.ucd.clops.runtime.options.CLOPSErrorOption;
import ie.ucd.clops.runtime.options.OptionGroup;
import ie.ucd.clops.runtime.options.OptionStore;
import ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException;
import java.util.List;
import java.io.File;
import ie.ucd.clops.runtime.options.BooleanOption;
import ie.ucd.clops.runtime.options.FileOption;
import ie.ucd.clops.runtime.options.EnumListOption;
import ie.ucd.clops.runtime.options.StringOption;
import ie.ucd.clops.runtime.options.FileListOption;

public class CLODSLOptionStore extends OptionStore implements CLODSLOptionsInterface {

  private final FileOption ogOutput;
  private final BooleanOption ogTest;
  private final StringOption ogOutputPackage;
  private final BooleanOption ogDocs;
  private final EnumListOption ogBuiltin;
  private final FileListOption ogCustom;
  private final FileOption ogTarget;
  private final BooleanOption ogVerbose;
  private final BooleanOption ogVersion;
  private final StringOption ogOptionFactory;
  private final BooleanOption ogTransitiveFlyRules;
  private final BooleanOption ogInfiniteLookahead;
  private final FileOption ogInput;
  private final CLOPSErrorOption CLOPSERROROPTION;

  public CLODSLOptionStore() throws InvalidOptionPropertyValueException {

    //Options
    ogOutput = new FileOption("Output", "(?:-o)|(?:--output)");
    addOption(ogOutput);
    ogOutput.setProperty("mustExist", "true");
    ogOutput.setProperty("mustbedir", "true");
    ogOutput.setProperty("default", ".");
    ogOutput.setProperty("description", "Output directory for generated Java files.");
    ogTest = new BooleanOption("Test", "(?:-m)|(?:--main)");
    addOption(ogTest);
    ogTest.setProperty("description", "Generate a Main class with a main method for rapid testing/debugging.");
    ogOutputPackage = new StringOption("OutputPackage", "(?:-p)|(?:--package)");
    addOption(ogOutputPackage);
    ogOutputPackage.setProperty("stripquotesifpresent", "true");
    ogOutputPackage.setProperty("blankparamallowed", "true");
    ogOutputPackage.setProperty("description", "Output Java package. If left empty, the default package is used.");
    ogDocs = new BooleanOption("Docs", "(?:-d)|(?:--docs)");
    addOption(ogDocs);
    ogDocs.setProperty("description", "Use a default documentation template for generation.");
    ogBuiltin = new EnumListOption("Builtin", "(?:-b)|(?:--built-in)");
    addOption(ogBuiltin);
    ogBuiltin.setProperty("choices", "htmldev,html,manpage,usage,help");
    ogBuiltin.setProperty("description", "Use a specific built-in documentation template for generation (you must specify one of the following: htmldev,html,manpage,usage).");
    ogCustom = new FileListOption("Custom", "(?:-c)|(?:--custom)");
    addOption(ogCustom);
    ogCustom.setProperty("mustExist", "true");
    ogCustom.setProperty("canBeDir", "false");
    ogCustom.setProperty("description", "Use custom templates for generation.");
    ogTarget = new FileOption("Target", "(?:-t)|(?:--target)");
    addOption(ogTarget);
    ogTarget.setProperty("description", "Specify the target directory / or the target file for the generation from some templates.");
    ogVerbose = new BooleanOption("Verbose", "(?:-v)|(?:--verbose)");
    addOption(ogVerbose);
    ogVerbose.setProperty("default", "false");
    ogVerbose.setProperty("description", "Print debugging messages.");
    ogVersion = new BooleanOption("Version", "(?:-version)");
    addOption(ogVersion);
    ogVersion.setProperty("description", "Print version information and exit");
    ogOptionFactory = new StringOption("OptionFactory", "(?:-of)|(?:--option-factory)");
    addOption(ogOptionFactory);
    ogOptionFactory.setProperty("description", "Use this option factory instead of the default. Must be a fully qualified class name.");
    ogTransitiveFlyRules = new BooleanOption("TransitiveFlyRules", "(?:-tfr)|(?:--transitive-fly-rules)");
    addOption(ogTransitiveFlyRules);
    ogTransitiveFlyRules.setProperty("default", "false");
    ogTransitiveFlyRules.setProperty("description", 
      "Fly rules in the generated parser will be applied" +
      "transitively. Meaning that assigning to an option in a fly-rule" +
      "triggers fly-rules associated with that opion. This is an advanced" +
      "and experimental feature. The issue with is it that the parser" +
      "becomes potentially non-terminating due to rules triggering one" +
      "another.");
    ogInfiniteLookahead = new BooleanOption("InfiniteLookahead", "(?:-oo)|(?:--infinite-lookahead)");
    addOption(ogInfiniteLookahead);
    ogInfiniteLookahead.setProperty("default", "false");
    ogInfiniteLookahead.setProperty("description", "The generated command-line parser will try harder to match inputs to the format.");
    ogInput = new FileOption("Input", "");
    addOption(ogInput);
    ogInput.setProperty("between", "");
    ogInput.setProperty("mustExist", "true");
    ogInput.setProperty("canbedir", "false");
    ogInput.setProperty("description", "Input CLOPS file.");
  
    CLOPSERROROPTION = new ie.ucd.clops.runtime.options.CLOPSErrorOption();
    addOption(CLOPSERROROPTION);
  
    //Option groups
    final OptionGroup ogAll = new OptionGroup("All");
    addOptionGroup(ogAll);
    final OptionGroup ogBase = new OptionGroup("Base");
    addOptionGroup(ogBase);
    final OptionGroup ogTemplates = new OptionGroup("Templates");
    addOptionGroup(ogTemplates);
    final OptionGroup ogAdvanced = new OptionGroup("Advanced");
    addOptionGroup(ogAdvanced);
    final OptionGroup ogAllOptions = new OptionGroup("AllOptions");
    addOptionGroup(ogAllOptions);
    
    //Setup groupings
    ogAll.addOptionOrGroup(ogOutputPackage);
    ogAll.addOptionOrGroup(ogVerbose);
    ogAll.addOptionOrGroup(ogOptionFactory);
    ogAll.addOptionOrGroup(ogOutput);
    ogAll.addOptionOrGroup(ogCustom);
    ogAll.addOptionOrGroup(ogTransitiveFlyRules);
    ogAll.addOptionOrGroup(ogTest);
    ogAll.addOptionOrGroup(ogTarget);
    ogAll.addOptionOrGroup(ogBuiltin);
    ogAll.addOptionOrGroup(ogInfiniteLookahead);
    ogAll.addOptionOrGroup(ogVersion);
    ogAll.addOptionOrGroup(ogDocs);
    ogBase.addOptionOrGroup(ogVerbose);
    ogBase.addOptionOrGroup(ogOutputPackage);
    ogBase.addOptionOrGroup(ogTest);
    ogBase.addOptionOrGroup(ogOutput);
    ogTemplates.addOptionOrGroup(ogTarget);
    ogTemplates.addOptionOrGroup(ogBuiltin);
    ogTemplates.addOptionOrGroup(ogCustom);
    ogTemplates.addOptionOrGroup(ogDocs);
    ogAdvanced.addOptionOrGroup(ogOptionFactory);
    ogAdvanced.addOptionOrGroup(ogInfiniteLookahead);
    ogAdvanced.addOptionOrGroup(ogTransitiveFlyRules);
    //AllOptions group
    ogAllOptions.addOptionOrGroup(ogOutput);
    ogAllOptions.addOptionOrGroup(ogTest);
    ogAllOptions.addOptionOrGroup(ogOutputPackage);
    ogAllOptions.addOptionOrGroup(ogDocs);
    ogAllOptions.addOptionOrGroup(ogBuiltin);
    ogAllOptions.addOptionOrGroup(ogCustom);
    ogAllOptions.addOptionOrGroup(ogTarget);
    ogAllOptions.addOptionOrGroup(ogVerbose);
    ogAllOptions.addOptionOrGroup(ogVersion);
    ogAllOptions.addOptionOrGroup(ogOptionFactory);
    ogAllOptions.addOptionOrGroup(ogTransitiveFlyRules);
    ogAllOptions.addOptionOrGroup(ogInfiniteLookahead);
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
  
// Option Test.
// Aliases: [-m, --main]
  
  /**
   * {@inheritDoc}
   */
  public boolean isTestSet() {
    return ogTest.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getTest() {
    return ogTest.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawTest() {
    return ogTest.getRawValue();
  }
  
  public BooleanOption getTestOption() {
    return ogTest;
  }
  
// Option OutputPackage.
// Aliases: [-p, --package]
  
  /**
   * {@inheritDoc}
   */
  public boolean isOutputPackageSet() {
    return ogOutputPackage.hasValue();
  }
  
  /** {@inheritDoc} */
  public String getOutputPackage() {
    return ogOutputPackage.getValue();
  }

  /** {@inheritDoc} */
  public String getRawOutputPackage() {
    return ogOutputPackage.getRawValue();
  }
  
  public StringOption getOutputPackageOption() {
    return ogOutputPackage;
  }
  
// Option Docs.
// Aliases: [-d, --docs]
  
  /**
   * {@inheritDoc}
   */
  public boolean isDocsSet() {
    return ogDocs.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getDocs() {
    return ogDocs.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawDocs() {
    return ogDocs.getRawValue();
  }
  
  public BooleanOption getDocsOption() {
    return ogDocs;
  }
  
// Option Builtin.
// Aliases: [-b, --built-in]
  
  /**
   * {@inheritDoc}
   */
  public boolean isBuiltinSet() {
    return ogBuiltin.hasValue();
  }
  

  /** {@inheritDoc} */
  public List<Builtin> getBuiltin() {
    return Builtin.get(ogBuiltin.getValue());
  }

  /** {@inheritDoc} */
  public List<String> getRawBuiltin() {
    return ogBuiltin.getRawValue();
  }
  
  public EnumListOption getBuiltinOption() {
    return ogBuiltin;
  }
  
// Option Custom.
// Aliases: [-c, --custom]
  
  /**
   * {@inheritDoc}
   */
  public boolean isCustomSet() {
    return ogCustom.hasValue();
  }
  
  /** {@inheritDoc} */
  public List<java.io.File> getCustom() {
    return ogCustom.getValue();
  }

  /** {@inheritDoc} */
  public List<java.io.File> getRawCustom() {
    return ogCustom.getRawValue();
  }
  
  public FileListOption getCustomOption() {
    return ogCustom;
  }
  
// Option Target.
// Aliases: [-t, --target]
  
  /**
   * {@inheritDoc}
   */
  public boolean isTargetSet() {
    return ogTarget.hasValue();
  }
  
  /** {@inheritDoc} */
  public File getTarget() {
    return ogTarget.getValue();
  }

  /** {@inheritDoc} */
  public File getRawTarget() {
    return ogTarget.getRawValue();
  }
  
  public FileOption getTargetOption() {
    return ogTarget;
  }
  
// Option Verbose.
// Aliases: [-v, --verbose]
  
  /**
   * {@inheritDoc}
   */
  public boolean isVerboseSet() {
    return ogVerbose.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getVerbose() {
    return ogVerbose.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawVerbose() {
    return ogVerbose.getRawValue();
  }
  
  public BooleanOption getVerboseOption() {
    return ogVerbose;
  }
  
// Option Version.
// Aliases: [-version]
  
  /**
   * {@inheritDoc}
   */
  public boolean isVersionSet() {
    return ogVersion.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getVersion() {
    return ogVersion.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawVersion() {
    return ogVersion.getRawValue();
  }
  
  public BooleanOption getVersionOption() {
    return ogVersion;
  }
  
// Option OptionFactory.
// Aliases: [-of, --option-factory]
  
  /**
   * {@inheritDoc}
   */
  public boolean isOptionFactorySet() {
    return ogOptionFactory.hasValue();
  }
  
  /** {@inheritDoc} */
  public String getOptionFactory() {
    return ogOptionFactory.getValue();
  }

  /** {@inheritDoc} */
  public String getRawOptionFactory() {
    return ogOptionFactory.getRawValue();
  }
  
  public StringOption getOptionFactoryOption() {
    return ogOptionFactory;
  }
  
// Option TransitiveFlyRules.
// Aliases: [-tfr, --transitive-fly-rules]
  
  /**
   * {@inheritDoc}
   */
  public boolean isTransitiveFlyRulesSet() {
    return ogTransitiveFlyRules.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getTransitiveFlyRules() {
    return ogTransitiveFlyRules.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawTransitiveFlyRules() {
    return ogTransitiveFlyRules.getRawValue();
  }
  
  public BooleanOption getTransitiveFlyRulesOption() {
    return ogTransitiveFlyRules;
  }
  
// Option InfiniteLookahead.
// Aliases: [-oo, --infinite-lookahead]
  
  /**
   * {@inheritDoc}
   */
  public boolean isInfiniteLookaheadSet() {
    return ogInfiniteLookahead.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getInfiniteLookahead() {
    return ogInfiniteLookahead.getValue();
  }

  /** {@inheritDoc} */
  public boolean getRawInfiniteLookahead() {
    return ogInfiniteLookahead.getRawValue();
  }
  
  public BooleanOption getInfiniteLookaheadOption() {
    return ogInfiniteLookahead;
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
  public File getInput() {
    return ogInput.getValue();
  }

  /** {@inheritDoc} */
  public File getRawInput() {
    return ogInput.getRawValue();
  }
  
  public FileOption getInputOption() {
    return ogInput;
  }
  
}
