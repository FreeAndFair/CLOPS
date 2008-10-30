package ie.ucd.clops.codegeneration;

import ie.ucd.clops.codegeneration.GeneratedCodeUnit.Visibility;
import ie.ucd.clops.dsl.structs.AssignmentDescription;
import ie.ucd.clops.dsl.structs.OptionDescription;
import ie.ucd.clops.dsl.structs.OptionGroupDescription;
import ie.ucd.clops.dsl.structs.FlyRuleDescription;

import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileOutputStream;
import java.io.PrintWriter;
import java.util.Collection;

public class CodeGenerator {


  //Input: OptionDescriptions
  //       Directory to output to
  //Ouput: Some .java files
  public static void createCode(String formatString, 
      Collection<OptionDescription> opDescriptions, 
      Collection<OptionGroupDescription> opGroupDescriptions, 
      Collection<FlyRuleDescription> overrideRuleDescriptions,
      File outputDir) {

    GeneratedClass specificParser = new GeneratedClass("Parser", Visibility.Public);
    addNecessaryImports(specificParser);
    specificParser.setSuperClass("ie.ucd.clops.runtime.parser.AbstractSpecificCLParser");
    specificParser.addMethod(new GeneratedConstructor("Parser", Visibility.Public));
    
    //Create the method that will initialise the OptionStore
    createOptionInitialisationCode(specificParser, opDescriptions, opGroupDescriptions);
    
    //Create the method that will initialise the override rules
    createOverrideRuleInitialisationCode(specificParser, overrideRuleDescriptions);

    GeneratedMethod createFormat = new GeneratedMethod("getFormatString", "String", Visibility.Public);
    createFormat.addStatement("return \"" + formatString + "\"");
    specificParser.addMethod(createFormat);
    
    try {
      writeGeneratedClasses(outputDir, specificParser);
    } catch (FileNotFoundException fnfe) {
      System.out.println("Error creating file. " + fnfe);
    }
    
    //new GeneratedCodePrinter(System.out).printClass(specificParser);
  }
  
  private static void addNecessaryImports(GeneratedClass genClass) {
    final String pack = "ie.ucd.clops.runtime.options";
    genClass.addImport(pack + ".Option");
    genClass.addImport(pack + ".OptionGroup");
    genClass.addImport(pack + ".OptionStore");
    genClass.addImport(pack + ".BooleanOption");
    genClass.addImport(pack + ".OptionAssignment");
    final String pack2 = "ie.ucd.clops.runtime.flyrules";
    genClass.addImport(pack2 + ".FlyRuleStore");
  }
  
  private static void writeGeneratedClasses(File outputDir, GeneratedClass... classes) throws FileNotFoundException {
    for (GeneratedClass genClass : classes) {
      writeGeneratedClass(outputDir, genClass);
    }
  }
  
  private static void writeGeneratedClass(File outputDir, GeneratedClass genClass) throws FileNotFoundException {
    PrintWriter pw = new PrintWriter(new FileOutputStream(outputDir.getAbsolutePath() + File.separator + genClass.getName() + ".java"));
    
    new GeneratedCodePrinter(pw).printClass(genClass);
    
    pw.flush();
    pw.close();
  }
  
  private static void createOptionInitialisationCode(GeneratedClass specificParser, Collection<OptionDescription> opDescriptions, Collection<OptionGroupDescription> opGroupDescriptions) {
  
    GeneratedMethod createOps = new GeneratedMethod("createOptions", "OptionStore", Visibility.Public);
    specificParser.addMethod(createOps);
    
    //Create the OptionStore method
    createOps.addStatement("OptionStore opStore = new OptionStore()");
    //Create and add each Option
    for (OptionDescription opDesc : opDescriptions) {
      //TODO need a code generator factory in line with the option factory
      createOps.addStatement("Option " + opDesc.getIdentifier() + " = new BooleanOption(\"" + opDesc.getIdentifier() + "\")");
      for (String alias : opDesc.getAliases()) {
        createOps.addStatement(opDesc.getIdentifier() + ".addAlias(\"" + alias + "\")");
      }
      createOps.addStatement("opStore.addOption(" + opDesc.getIdentifier() + ")");
    }
    
    //Create and add each OptionGroup
    for (OptionGroupDescription opGroupDesc : opGroupDescriptions) {
      createOps.addStatement("OptionGroup " + opGroupDesc.getIdentifier() + " = new OptionGroup(\"" + opGroupDesc.getIdentifier() + "\")");
      createOps.addStatement("opStore.addOptionGroup(" + opGroupDesc.getIdentifier() + ")");
    }
    
    //Loop again, this time adding the children
    for (OptionGroupDescription opGroupDesc : opGroupDescriptions) {
      for (String child : opGroupDesc.getChildren()) {
        createOps.addStatement(opGroupDesc.getIdentifier() + ".addOptionOrGroup(" + child + ")");
      }
    }

    //Finally, return the OptionStore
    createOps.addStatement("return opStore");
  }
  
  private static void createOverrideRuleInitialisationCode(GeneratedClass specificParser, Collection<FlyRuleDescription> overrideRuleDescriptions) {
    
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
  
}
