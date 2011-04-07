package ie.ucd.clops.dsl.generatedinterface;

import ie.ucd.clops.runtime.options.CLOPSErrorOption;
import ie.ucd.clops.runtime.options.OptionGroup;
import ie.ucd.clops.runtime.options.OptionStore;
import ie.ucd.clops.runtime.options.exception.InvalidOptionPropertyValueException;
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
  private final BooleanOption ogStaticCheck;
  private final BooleanOption ogVerbose;
  private final BooleanOption ogQuiet;
  private final BooleanOption ogVersion;
  private final StringOption ogOptionFactory;
  private final BooleanOption ogTransitiveFlyRules;
  private final FileOption ogInput;
  private final CLOPSErrorOption CLOPSERROROPTION;

  public CLODSLOptionStore() throws InvalidOptionPropertyValueException {

    //Options
    ogOutput = new FileOption("Output", "(?:-o)|(?:--output)");
    addOption(ogOutput);
    ogOutput.setProperty("mustExist", "true");
    ogOutput.setProperty("mustbedir", "true");
    ogOutput.setProperty("default", ".");
    ogOutput.setProperty("aliases", "-o,--output");
    ogOutput.setProperty("description", "Output directory for generated Java files.");
    ogTest = new BooleanOption("Test", "(?:-m)|(?:--main)");
    addOption(ogTest);
    ogTest.setProperty("aliases", "-m,--main");
    ogTest.setProperty("description", "Generate a Main class with a main method for rapid testing/debugging.");
    ogOutputPackage = new StringOption("OutputPackage", "(?:-p)|(?:--package)");
    addOption(ogOutputPackage);
    ogOutputPackage.setProperty("stripquotesifpresent", "true");
    ogOutputPackage.setProperty("blankparamallowed", "true");
    ogOutputPackage.setProperty("defaultvalue", "");
    ogOutputPackage.setProperty("aliases", "-p,--package");
    ogOutputPackage.setProperty("description", "Output Java package. If left empty, the default package is used.");
    ogDocs = new BooleanOption("Docs", "(?:-d)|(?:--docs)");
    addOption(ogDocs);
    ogDocs.setProperty("aliases", "-d,--docs");
    ogDocs.setProperty("description", "Use a default documentation template for generation.");
    ogBuiltin = new EnumListOption("Builtin", "(?:-b)|(?:--built-in)");
    addOption(ogBuiltin);
    ogBuiltin.setProperty("choices", "htmldev,html,manpage,usage,help");
    ogBuiltin.setProperty("aliases", "-b,--built-in");
    ogBuiltin.setProperty("description", "Use a specific built-in documentation template for generation (you must specify one of the following: htmldev,html,manpage,usage).");
    ogCustom = new FileListOption("Custom", "(?:-c)|(?:--custom)");
    addOption(ogCustom);
    ogCustom.setProperty("mustExist", "true");
    ogCustom.setProperty("canBeDir", "false");
    ogCustom.setProperty("aliases", "-c,--custom");
    ogCustom.setProperty("description", "Use custom templates for generation.");
    ogTarget = new FileOption("Target", "(?:-t)|(?:--target)");
    addOption(ogTarget);
    ogTarget.setProperty("default", ".");
    ogTarget.setProperty("mustbedir", "true");
    ogTarget.setProperty("mustexist", "true");
    ogTarget.setProperty("aliases", "-t,--target");
    ogTarget.setProperty("description", "Specify the target directory / or the target file for the generation from some templates.");
    ogStaticCheck = new BooleanOption("StaticCheck", "(?:-sc)|(?:--static-check)");
    addOption(ogStaticCheck);
    ogStaticCheck.setProperty("default", "true");
    ogStaticCheck.setProperty("aliases", "-sc,--static-check");
    ogStaticCheck.setProperty("description", "Perform static checks on the input data.");
    ogVerbose = new BooleanOption("Verbose", "(?:-v)|(?:--verbose)");
    addOption(ogVerbose);
    ogVerbose.setProperty("default", "false");
    ogVerbose.setProperty("aliases", "-v,--verbose");
    ogVerbose.setProperty("description", "Print debugging messages.");
    ogQuiet = new BooleanOption("Quiet", "(?:-q)|(?:--quiet)");
    addOption(ogQuiet);
    ogQuiet.setProperty("default", "false");
    ogQuiet.setProperty("aliases", "-q,--quiet");
    ogQuiet.setProperty("description", "Print only error messages.");
    ogVersion = new BooleanOption("Version", "(?:-version)");
    addOption(ogVersion);
    ogVersion.setProperty("aliases", "-version");
    ogVersion.setProperty("description", "Print version information and exit");
    ogOptionFactory = new StringOption("OptionFactory", "(?:-of)|(?:--option-factory)");
    addOption(ogOptionFactory);
    ogOptionFactory.setProperty("aliases", "-of,--option-factory");
    ogOptionFactory.setProperty("description", "Use this option factory instead of the default. Must be a fully qualified class name.");
    ogTransitiveFlyRules = new BooleanOption("TransitiveFlyRules", "(?:-tfr)|(?:--transitive-fly-rules)");
    addOption(ogTransitiveFlyRules);
    ogTransitiveFlyRules.setProperty("default", "false");
    ogTransitiveFlyRules.setProperty("aliases", "-tfr,--transitive-fly-rules");
    ogTransitiveFlyRules.setProperty("description", "Fly rules in the generated parser will be applied   transitively. Meaning that assigning to an option in a fly-rule   triggers fly-rules associated with that opion. This is an advanced   and experimental feature. The issue with it is that the parser   becomes potentially non-terminating due to rules triggering one   another.");
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
    ogAll.addOptionOrGroup(ogQuiet);
    ogAll.addOptionOrGroup(ogTest);
    ogAll.addOptionOrGroup(ogTarget);
    ogAll.addOptionOrGroup(ogBuiltin);
    ogAll.addOptionOrGroup(ogVersion);
    ogAll.addOptionOrGroup(ogDocs);
    ogAll.addOptionOrGroup(ogStaticCheck);
    ogBase.addOptionOrGroup(ogVerbose);
    ogBase.addOptionOrGroup(ogOutputPackage);
    ogBase.addOptionOrGroup(ogTest);
    ogBase.addOptionOrGroup(ogOutput);
    ogTemplates.addOptionOrGroup(ogTarget);
    ogTemplates.addOptionOrGroup(ogBuiltin);
    ogTemplates.addOptionOrGroup(ogCustom);
    ogTemplates.addOptionOrGroup(ogDocs);
    ogAdvanced.addOptionOrGroup(ogOptionFactory);
    ogAdvanced.addOptionOrGroup(ogTransitiveFlyRules);
    //AllOptions group
    ogAllOptions.addOptionOrGroup(ogOutput);
    ogAllOptions.addOptionOrGroup(ogTest);
    ogAllOptions.addOptionOrGroup(ogOutputPackage);
    ogAllOptions.addOptionOrGroup(ogDocs);
    ogAllOptions.addOptionOrGroup(ogBuiltin);
    ogAllOptions.addOptionOrGroup(ogCustom);
    ogAllOptions.addOptionOrGroup(ogTarget);
    ogAllOptions.addOptionOrGroup(ogStaticCheck);
    ogAllOptions.addOptionOrGroup(ogVerbose);
    ogAllOptions.addOptionOrGroup(ogQuiet);
    ogAllOptions.addOptionOrGroup(ogVersion);
    ogAllOptions.addOptionOrGroup(ogOptionFactory);
    ogAllOptions.addOptionOrGroup(ogTransitiveFlyRules);
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

  /** Gets the value of option Output without checking if it is set.
   *  This method will not throw an exception, but may return null. 
   */
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

  /** Gets the value of option Test without checking if it is set.
   *  This method will not throw an exception, but may return null. 
   */
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

  /** Gets the value of option OutputPackage without checking if it is set.
   *  This method will not throw an exception, but may return null. 
   */
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

  /** Gets the value of option Docs without checking if it is set.
   *  This method will not throw an exception, but may return null. 
   */
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

  /** Gets the value of option Builtin without checking if it is set.
   *  This method will not throw an exception, but may return null. 
   */
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

  /** Gets the value of option Custom without checking if it is set.
   *  This method will not throw an exception, but may return null. 
   */
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

  /** Gets the value of option Target without checking if it is set.
   *  This method will not throw an exception, but may return null. 
   */
  public File getRawTarget() {
    return ogTarget.getRawValue();
  }
  
  public FileOption getTargetOption() {
    return ogTarget;
  }
  
// Option StaticCheck.
// Aliases: [-sc, --static-check]
  
  /**
   * {@inheritDoc}
   */
  public boolean isStaticCheckSet() {
    return ogStaticCheck.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getStaticCheck() {
    return ogStaticCheck.getValue();
  }

  /** Gets the value of option StaticCheck without checking if it is set.
   *  This method will not throw an exception, but may return null. 
   */
  public boolean getRawStaticCheck() {
    return ogStaticCheck.getRawValue();
  }
  
  public BooleanOption getStaticCheckOption() {
    return ogStaticCheck;
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

  /** Gets the value of option Verbose without checking if it is set.
   *  This method will not throw an exception, but may return null. 
   */
  public boolean getRawVerbose() {
    return ogVerbose.getRawValue();
  }
  
  public BooleanOption getVerboseOption() {
    return ogVerbose;
  }
  
// Option Quiet.
// Aliases: [-q, --quiet]
  
  /**
   * {@inheritDoc}
   */
  public boolean isQuietSet() {
    return ogQuiet.hasValue();
  }
  
  /** {@inheritDoc} */
  public boolean getQuiet() {
    return ogQuiet.getValue();
  }

  /** Gets the value of option Quiet without checking if it is set.
   *  This method will not throw an exception, but may return null. 
   */
  public boolean getRawQuiet() {
    return ogQuiet.getRawValue();
  }
  
  public BooleanOption getQuietOption() {
    return ogQuiet;
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

  /** Gets the value of option Version without checking if it is set.
   *  This method will not throw an exception, but may return null. 
   */
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

  /** Gets the value of option OptionFactory without checking if it is set.
   *  This method will not throw an exception, but may return null. 
   */
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

  /** Gets the value of option TransitiveFlyRules without checking if it is set.
   *  This method will not throw an exception, but may return null. 
   */
  public boolean getRawTransitiveFlyRules() {
    return ogTransitiveFlyRules.getRawValue();
  }
  
  public BooleanOption getTransitiveFlyRulesOption() {
    return ogTransitiveFlyRules;
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

  /** Gets the value of option Input without checking if it is set.
   *  This method will not throw an exception, but may return null. 
   */
  public File getRawInput() {
    return ogInput.getRawValue();
  }
  
  public FileOption getInputOption() {
    return ogInput;
  }
  
}
