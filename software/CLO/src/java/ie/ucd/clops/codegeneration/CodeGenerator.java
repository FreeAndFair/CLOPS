package ie.ucd.clops.codegeneration;

import ie.ucd.clops.codegeneration.GeneratedCodeUnit.Visibility;
import ie.ucd.clops.dsl.structs.OptionDescription;
import ie.ucd.clops.dsl.structs.OptionGroupDescription;

import java.io.File;
import java.util.Collection;

public class CodeGenerator {


  //Input: OptionDescriptions
  //       Directory to output to
  //Ouput: Some .java files

  public static void createCode(Collection<OptionDescription> opDescriptions, Collection<OptionGroupDescription> opGroupDescriptions, File outputDir) {

    GeneratedClass specificParser = new GeneratedClass("Parser", Visibility.Public);

    //Create the method that will initialise the OptionStore
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
        createOps.addStatement(opGroupDesc.getIdentifier() + ".addOptionOrGroup(" + child + "\")");
      }
    }

    //Finally, return the OptionStore
    createOps.addStatement("return opStore");

    specificParser.addMethod(new GeneratedConstructor("Parser", Visibility.Public));

    new GeneratedCodePrinter(System.out).printClass(specificParser);

    

  }
  
}
