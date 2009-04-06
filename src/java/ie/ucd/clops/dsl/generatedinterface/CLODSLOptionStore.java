package ie.ucd.clops.dsl.generatedinterface;

import ie.ucd.clops.runtime.options.CLOPSErrorOption;
import ie.ucd.clops.runtime.options.OptionGroup;
import ie.ucd.clops.runtime.options.OptionStore;

public class CLODSLOptionStore extends OptionStore implements CLODSLOptionsInterface {

  private final ie.ucd.clops.runtime.options.FileOption OutputOG;
  private final ie.ucd.clops.runtime.options.BooleanOption TestOG;
  private final ie.ucd.clops.runtime.options.StringOption OutputPackageOG;
  private final ie.ucd.clops.runtime.options.StringOption OptionFactoryOG;
  private final ie.ucd.clops.runtime.options.BooleanOption DocsOG;
  private final ie.ucd.clops.runtime.options.StringEnumOption BuiltinOG;
  private final ie.ucd.clops.runtime.options.FileListOption CustomOG;
  private final ie.ucd.clops.runtime.options.FileOption TargetOG;
  private final ie.ucd.clops.runtime.options.BooleanOption VerboseOG;
  private final ie.ucd.clops.runtime.options.BooleanOption TransitiveFlyRulesOG;
  private final ie.ucd.clops.runtime.options.BooleanOption InfiniteLookaheadOG;
  private final ie.ucd.clops.runtime.options.FileOption InputOG;
  private final CLOPSErrorOption CLOPSERROROPTION;

  public CLODSLOptionStore() throws ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException {

    //Options
    OutputOG = new ie.ucd.clops.runtime.options.FileOption("Output", "(?:-o)|(?:--output)");
    addOption(OutputOG);
    OutputOG.setProperty("mustExist", "true");
    OutputOG.setProperty("mustbedir", "true");
    OutputOG.setProperty("default", ".");
    OutputOG.setProperty("description", "Output directory for generated Java files.");
    TestOG = new ie.ucd.clops.runtime.options.BooleanOption("Test", "(?:-m)|(?:--main)");
    addOption(TestOG);
    TestOG.setProperty("description", "Generate a Main class with a main method for rapid testing/debugging.");
    OutputPackageOG = new ie.ucd.clops.runtime.options.StringOption("OutputPackage", "(?:-p)|(?:--package)");
    addOption(OutputPackageOG);
    OutputPackageOG.setProperty("stripquotesifpresent", "true");
    OutputPackageOG.setProperty("description", "Output package. If left empty the default package is used.");
    OptionFactoryOG = new ie.ucd.clops.runtime.options.StringOption("OptionFactory", "(?:-of)|(?:--option-factory)");
    addOption(OptionFactoryOG);
    OptionFactoryOG.setProperty("description", "Use this option factory instead of the default. Must be a fully qualified class name.");
    DocsOG = new ie.ucd.clops.runtime.options.BooleanOption("Docs", "(?:-d)|(?:--docs)");
    addOption(DocsOG);
    DocsOG.setProperty("description", "Use a default documentation template for generation.");
    BuiltinOG = new ie.ucd.clops.runtime.options.StringEnumOption("Builtin", "(?:-b)|(?:--built-in)");
    addOption(BuiltinOG);
    BuiltinOG.setProperty("choices", "htmldev,html,manpage,usage,help");
    BuiltinOG.setProperty("description", "Use a specific built-in documentation template for generation (you must specify one of the following: htmldev,html,manpage,usage).");
    CustomOG = new ie.ucd.clops.runtime.options.FileListOption("Custom", "(?:-c)|(?:--custom)");
    addOption(CustomOG);
    CustomOG.setProperty("mustExist", "true");
    CustomOG.setProperty("canBeDir", "false");
    CustomOG.setProperty("description", "Use custom templates for generation.");
    TargetOG = new ie.ucd.clops.runtime.options.FileOption("Target", "(?:-t)|(?:--target)");
    addOption(TargetOG);
    TargetOG.setProperty("description", "Specify the target directory / or the target file for the generation from some templates.");
    VerboseOG = new ie.ucd.clops.runtime.options.BooleanOption("Verbose", "(?:-v)|(?:--verbose)");
    addOption(VerboseOG);
    VerboseOG.setProperty("default", "false");
    VerboseOG.setProperty("description", "Print debugging messages.");
    TransitiveFlyRulesOG = new ie.ucd.clops.runtime.options.BooleanOption("TransitiveFlyRules", "(?:-tfr)|(?:--transitive-fly-rules)");
    addOption(TransitiveFlyRulesOG);
    TransitiveFlyRulesOG.setProperty("default", "false");
    TransitiveFlyRulesOG.setProperty("description", "Fly rules will applied transitively.");
    InfiniteLookaheadOG = new ie.ucd.clops.runtime.options.BooleanOption("InfiniteLookahead", "(?:-oo)|(?:--infinite-lookahead)");
    addOption(InfiniteLookaheadOG);
    InfiniteLookaheadOG.setProperty("default", "false");
    InfiniteLookaheadOG.setProperty("description", "The command line parser will try harder.");
    InputOG = new ie.ucd.clops.runtime.options.FileOption("Input", "");
    addOption(InputOG);
    InputOG.setProperty("between", "");
    InputOG.setProperty("mustExist", "true");
    InputOG.setProperty("canbedir", "false");
    InputOG.setProperty("description", "Input file.");
  
    CLOPSERROROPTION = new ie.ucd.clops.runtime.options.CLOPSErrorOption();
    addOption(CLOPSERROROPTION);
  
    //Option groups
    final OptionGroup all_argsOG = new OptionGroup("all_args");
    addOptionGroup(all_argsOG);
    final OptionGroup TemplatesOG = new OptionGroup("Templates");
    addOptionGroup(TemplatesOG);
    //Setup groupings
    all_argsOG.addOptionOrGroup(OutputOG);
    all_argsOG.addOptionOrGroup(OutputPackageOG);
    all_argsOG.addOptionOrGroup(OptionFactoryOG);
    all_argsOG.addOptionOrGroup(TestOG);
    all_argsOG.addOptionOrGroup(VerboseOG);
    all_argsOG.addOptionOrGroup(TransitiveFlyRulesOG);
    all_argsOG.addOptionOrGroup(TemplatesOG);
    TemplatesOG.addOptionOrGroup(DocsOG);
    TemplatesOG.addOptionOrGroup(BuiltinOG);
    TemplatesOG.addOptionOrGroup(CustomOG);
    TemplatesOG.addOptionOrGroup(TargetOG);
  }
  
// Option Output.
// Aliases: [-o, --output]
  
  /**
   * {@inheritDoc}
   */
  public boolean isOutputSet() {
    return OutputOG.hasValue();
  }
  
       
  /**
   * {@inheritDoc}
   */
  public java.io.File getOutput() {
        return OutputOG.getValue();
     }

  /**
   * {@inheritDoc}
   */
  public java.io.File getRawOutput() {
    return OutputOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.FileOption getOutputOption() {
    return OutputOG;
  }
  
// Option Test.
// Aliases: [-m, --main]
  
  /**
   * {@inheritDoc}
   */
  public boolean isTestSet() {
    return TestOG.hasValue();
  }
  
       
  /**
   * {@inheritDoc}
   */
  public boolean getTest() {
        return TestOG.getValue();
     }

  /**
   * {@inheritDoc}
   */
  public boolean getRawTest() {
    return TestOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.BooleanOption getTestOption() {
    return TestOG;
  }
  
// Option OutputPackage.
// Aliases: [-p, --package]
  
  /**
   * {@inheritDoc}
   */
  public boolean isOutputPackageSet() {
    return OutputPackageOG.hasValue();
  }
  
       
  /**
   * {@inheritDoc}
   */
  public String getOutputPackage() {
        return OutputPackageOG.getValue();
     }

  /**
   * {@inheritDoc}
   */
  public String getRawOutputPackage() {
    return OutputPackageOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.StringOption getOutputPackageOption() {
    return OutputPackageOG;
  }
  
// Option OptionFactory.
// Aliases: [-of, --option-factory]
  
  /**
   * {@inheritDoc}
   */
  public boolean isOptionFactorySet() {
    return OptionFactoryOG.hasValue();
  }
  
       
  /**
   * {@inheritDoc}
   */
  public String getOptionFactory() {
        return OptionFactoryOG.getValue();
     }

  /**
   * {@inheritDoc}
   */
  public String getRawOptionFactory() {
    return OptionFactoryOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.StringOption getOptionFactoryOption() {
    return OptionFactoryOG;
  }
  
// Option Docs.
// Aliases: [-d, --docs]
  
  /**
   * {@inheritDoc}
   */
  public boolean isDocsSet() {
    return DocsOG.hasValue();
  }
  
       
  /**
   * {@inheritDoc}
   */
  public boolean getDocs() {
        return DocsOG.getValue();
     }

  /**
   * {@inheritDoc}
   */
  public boolean getRawDocs() {
    return DocsOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.BooleanOption getDocsOption() {
    return DocsOG;
  }
  
// Option Builtin.
// Aliases: [-b, --built-in]
  
  /**
   * {@inheritDoc}
   */
  public boolean isBuiltinSet() {
    return BuiltinOG.hasValue();
  }
  
     	
    
  /**
   * {@inheritDoc}
   */
  public Builtin getBuiltin() {
       return Builtin.get(BuiltinOG.getValue());
     }

  /**
   * {@inheritDoc}
   */
  public String getRawBuiltin() {
    return BuiltinOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.StringEnumOption getBuiltinOption() {
    return BuiltinOG;
  }
  
// Option Custom.
// Aliases: [-c, --custom]
  
  /**
   * {@inheritDoc}
   */
  public boolean isCustomSet() {
    return CustomOG.hasValue();
  }
  
       
  /**
   * {@inheritDoc}
   */
  public java.util.List<java.io.File> getCustom() {
        return CustomOG.getValue();
     }

  /**
   * {@inheritDoc}
   */
  public java.util.List<java.io.File> getRawCustom() {
    return CustomOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.FileListOption getCustomOption() {
    return CustomOG;
  }
  
// Option Target.
// Aliases: [-t, --target]
  
  /**
   * {@inheritDoc}
   */
  public boolean isTargetSet() {
    return TargetOG.hasValue();
  }
  
       
  /**
   * {@inheritDoc}
   */
  public java.io.File getTarget() {
        return TargetOG.getValue();
     }

  /**
   * {@inheritDoc}
   */
  public java.io.File getRawTarget() {
    return TargetOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.FileOption getTargetOption() {
    return TargetOG;
  }
  
// Option Verbose.
// Aliases: [-v, --verbose]
  
  /**
   * {@inheritDoc}
   */
  public boolean isVerboseSet() {
    return VerboseOG.hasValue();
  }
  
       
  /**
   * {@inheritDoc}
   */
  public boolean getVerbose() {
        return VerboseOG.getValue();
     }

  /**
   * {@inheritDoc}
   */
  public boolean getRawVerbose() {
    return VerboseOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.BooleanOption getVerboseOption() {
    return VerboseOG;
  }
  
// Option TransitiveFlyRules.
// Aliases: [-tfr, --transitive-fly-rules]
  
  /**
   * {@inheritDoc}
   */
  public boolean isTransitiveFlyRulesSet() {
    return TransitiveFlyRulesOG.hasValue();
  }
  
       
  /**
   * {@inheritDoc}
   */
  public boolean getTransitiveFlyRules() {
        return TransitiveFlyRulesOG.getValue();
     }

  /**
   * {@inheritDoc}
   */
  public boolean getRawTransitiveFlyRules() {
    return TransitiveFlyRulesOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.BooleanOption getTransitiveFlyRulesOption() {
    return TransitiveFlyRulesOG;
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
  
// Option Input.
// Aliases: []
  
  /**
   * {@inheritDoc}
   */
  public boolean isInputSet() {
    return InputOG.hasValue();
  }
  
       
  /**
   * {@inheritDoc}
   */
  public java.io.File getInput() {
        return InputOG.getValue();
     }

  /**
   * {@inheritDoc}
   */
  public java.io.File getRawInput() {
    return InputOG.getRawValue();
  }
  
  public ie.ucd.clops.runtime.options.FileOption getInputOption() {
    return InputOG;
  }
  
}
