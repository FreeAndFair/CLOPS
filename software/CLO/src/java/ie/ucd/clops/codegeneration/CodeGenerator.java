package ie.ucd.clops.codegeneration;

import ie.ucd.clops.codegeneration.GeneratedCodeUnit.Visibility;
import ie.ucd.clops.dsl.structs.AssignmentDescription;
import ie.ucd.clops.dsl.structs.FlyRuleDescription;
import ie.ucd.clops.dsl.structs.OptionDescription;
import ie.ucd.clops.dsl.structs.OptionGroupDescription;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintWriter;
import java.util.Collection;
import java.util.Map.Entry;

public class CodeGenerator {


  public static void createCode(String formatString, 
      Collection<OptionDescription> opDescriptions, 
      Collection<OptionGroupDescription> opGroupDescriptions, 
      Collection<FlyRuleDescription> overrideRuleDescriptions,
      File outputDir,
      String outputPackage) {

    //Specific parser
    GeneratedClassOrInterface specificParser = createSpecificParser(formatString, opDescriptions, opGroupDescriptions, overrideRuleDescriptions, outputPackage);
    
    //OptionsInterface
    GeneratedClassOrInterface optionsInterface = createOptionsInterface(opDescriptions, outputPackage);
    
    //SpecifiOptionsStore
    GeneratedClassOrInterface specificOptionStore = createSpecificOptionStore(opDescriptions, opGroupDescriptions, outputPackage);
    
    try {
      writeGeneratedClasses(outputDir, specificParser, optionsInterface, specificOptionStore);
    } catch (FileNotFoundException fnfe) {
      System.out.println("Error creating file. " + fnfe);
    }
    
  }
  
  private static void addNecessaryImports(GeneratedClassOrInterface genClass) {
    final String pack = "ie.ucd.clops.runtime.options";
    genClass.addImport(pack + ".Option");
    genClass.addImport(pack + ".OptionGroup");
    genClass.addImport(pack + ".OptionStore");
    genClass.addImport(pack + ".BooleanOption");
    genClass.addImport(pack + ".OptionAssignment");
    final String pack2 = "ie.ucd.clops.runtime.flyrules";
    genClass.addImport(pack2 + ".FlyRuleStore");
  }
  
  private static void writeGeneratedClasses(File outputDir, GeneratedClassOrInterface... classes) throws FileNotFoundException {
    for (GeneratedClassOrInterface genClass : classes) {
      writeGeneratedClass(outputDir, genClass);
    }
  }
  
  private static void writeGeneratedClass(File outputDir, GeneratedClassOrInterface... genClasses) throws FileNotFoundException {
    for (GeneratedClassOrInterface genClass : genClasses) {
      PrintWriter pw = new PrintWriter(new FileOutputStream(outputDir.getAbsolutePath() + File.separator + genClass.getName() + ".java"));
      new GeneratedCodePrinter(pw).printClass(genClass);
      pw.flush();
      pw.close();
    }
  }
  
  private static GeneratedMethod createOptionInitialisationMethod(GeneratedClassOrInterface specificParser, Collection<OptionDescription> opDescriptions, Collection<OptionGroupDescription> opGroupDescriptions) {
  
    GeneratedMethod createOps = new GeneratedMethod("createOptions", "OptionStore", Visibility.Public);
    //specificParser.addMethod(createOps);
    createOps.addException("ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException");
    
    createOps.addStatement("return new SpecificOptionStore()");
    
    return createOps;
  }
  
  private static void createOverrideRuleInitialisationCode(GeneratedClassOrInterface specificParser, Collection<FlyRuleDescription> overrideRuleDescriptions) {
    
    GeneratedMethod createOverrideRules = new GeneratedMethod("createFlyRules", "FlyRuleStore", Visibility.Public);
    specificParser.addMethod(createOverrideRules);
    
    createOverrideRules.addStatement("FlyRuleStore flyStore = new FlyRuleStore()");
    
    for (FlyRuleDescription orDescription : overrideRuleDescriptions) {
      String opId = orDescription.getTriggeringOptionIdentifier();
      for (AssignmentDescription desc : orDescription.getAssignments()) {
        //TODO conversion from String to specific Option value object type here...
        createOverrideRules.addStatement("flyStore.addAssignmentForOption(\"" + opId + "\", new OptionAssignment(\"" + desc.getOptionIdentifier() + "\", \"" + desc.getValue() + "\"))");
      }
    }
    
    createOverrideRules.addStatement("return flyStore");
  }
  
  private static GeneratedClassOrInterface createOptionsInterface(Collection<OptionDescription> opDescriptions, String outputPackage) {
    GeneratedClassOrInterface optionsInterface = new GeneratedClassOrInterface("OptionsInterface", true, outputPackage, Visibility.Public);
    for (OptionDescription od : opDescriptions) {
      GeneratedMethod isSetMethod = new GeneratedMethod("is" + od.getIdentifier() + "Set", "boolean", Visibility.Public);
      isSetMethod.setAbstract(true);
      GeneratedMethod getValueMethod = new GeneratedMethod("get" + od.getIdentifier(), od.getType().getOptionValueTypeClass(), Visibility.Public);
      getValueMethod.setAbstract(true);
      optionsInterface.addMethod(isSetMethod);
      optionsInterface.addMethod(getValueMethod);
    }
    return optionsInterface;
  }

  private static GeneratedClassOrInterface createSpecificParser(
      String formatString,
      Collection<OptionDescription> opDescriptions, 
      Collection<OptionGroupDescription> opGroupDescriptions,
      Collection<FlyRuleDescription> overrideRuleDescriptions,
      String outputPackage) {
    GeneratedClassOrInterface specificParser = new GeneratedClassOrInterface("Parser", false, outputPackage, Visibility.Public);
    addNecessaryImports(specificParser);
    specificParser.setSuperClass("ie.ucd.clops.runtime.parser.AbstractSpecificCLParser");
    specificParser.addMethod(new GeneratedConstructor("Parser", Visibility.Public));
    
    //Create the method that will initialise the OptionStore
    specificParser.addMethod(createOptionInitialisationMethod(specificParser, opDescriptions, opGroupDescriptions));
    
    //Create the method that will initialise the override rules
    createOverrideRuleInitialisationCode(specificParser, overrideRuleDescriptions);

    GeneratedMethod createFormat = new GeneratedMethod("getFormatString", "String", Visibility.Public);
    createFormat.addStatement("return \"" + formatString + "\"");
    specificParser.addMethod(createFormat);
    return specificParser;
  }
  
  private static GeneratedClassOrInterface createSpecificOptionStore(
      Collection<OptionDescription> opDescriptions, 
      Collection<OptionGroupDescription> opGroupDescriptions,
      String outputPackage) {
    final String className = "SpecificOptionStore";
    
    GeneratedClassOrInterface specificOptionStore = new GeneratedClassOrInterface(className, false, outputPackage, Visibility.Public);
    specificOptionStore.setSuperClass("ie.ucd.clops.runtime.options.OptionStore");
    specificOptionStore.addImplementedInterface("OptionsInterface");
    final String pack = "ie.ucd.clops.runtime.options";
    specificOptionStore.addImport(pack + ".OptionGroup");
    
    for (OptionDescription opDesc : opDescriptions) {
      GeneratedField field = new GeneratedField(opDesc.getIdentifier(), opDesc.getType().getOptionTypeClass(), Visibility.Private);
      field.addModifier("final");
      specificOptionStore.addField(field);
    }
    
    GeneratedConstructor constructor = new GeneratedConstructor(className, Visibility.Public);
    constructor.addException("ie.ucd.clops.runtime.options.InvalidOptionPropertyValueException");
    
    //Create and add each Option
    for (OptionDescription opDesc : opDescriptions) {
      //TODO need a code generator factory in line with the option factory
      constructor.addStatement(opDesc.getIdentifier() + " = new " + opDesc.getType().getOptionTypeClass() + "(\"" + opDesc.getIdentifier() + "\")"); 

      for (String alias : opDesc.getAliases()) {
        constructor.addStatement(opDesc.getIdentifier() + ".addAlias(\"" + alias + "\")");
      }
      for (Entry<String,String> entry : opDesc.getProperties().entrySet()) {
        constructor.addStatement(opDesc.getIdentifier() + ".setProperty(\"" + entry.getKey() + "\",\"" + entry.getValue() + "\")");
      }
      constructor.addStatement("addOption(" + opDesc.getIdentifier() + ")");
    }
    
    //Create and add each OptionGroup
    for (OptionGroupDescription opGroupDesc : opGroupDescriptions) {
      constructor.addStatement("OptionGroup " + opGroupDesc.getIdentifier() + " = new OptionGroup(\"" + opGroupDesc.getIdentifier() + "\")");
      constructor.addStatement("addOptionGroup(" + opGroupDesc.getIdentifier() + ")");
    }
    
    //Loop again, this time adding the children
    for (OptionGroupDescription opGroupDesc : opGroupDescriptions) {
      for (String child : opGroupDesc.getChildren()) {
        constructor.addStatement(opGroupDesc.getIdentifier() + ".addOptionOrGroup(" + child + ")");
      }
    }

    specificOptionStore.addMethod(constructor);
    
    
    for (OptionDescription od : opDescriptions) {
      GeneratedMethod isSetMethod = new GeneratedMethod("is" + od.getIdentifier() + "Set", "boolean", Visibility.Public);
      isSetMethod.addStatement("return " + od.getIdentifier() + ".hasValue()");
      GeneratedMethod getValueMethod = new GeneratedMethod("get" + od.getIdentifier(), od.getType().getOptionValueTypeClass(), Visibility.Public);
      getValueMethod.addStatement("return " + od.getIdentifier() + '.' + od.getType().getOptionValueGetterMethodName() + "()");
      specificOptionStore.addMethod(isSetMethod);
      specificOptionStore.addMethod(getValueMethod);
    }
    
    return specificOptionStore;
  }
  
}
