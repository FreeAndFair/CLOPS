package ie.ucd.clops.codegeneration;

import ie.ucd.clops.codegeneration.java.GeneratedClass;
import ie.ucd.clops.codegeneration.java.GeneratedCodePrinter;
import ie.ucd.clops.codegeneration.java.GeneratedConstructor;
import ie.ucd.clops.codegeneration.java.GeneratedMethod;
import ie.ucd.clops.codegeneration.java.GeneratedStatement;
import ie.ucd.clops.codegeneration.java.GeneratedCodeUnit.Visibility;
import ie.ucd.clops.dsl.structs.OptionDescription;

import java.io.File;
import java.util.Set;

public class CodeGenerator {

  
  //Input: OptionDescriptions
  //       Directory to output to
  //Ouput: Some .java files
  
  public static void createCode(Set<OptionDescription> opDescriptions, File outputDir) {
    
    GeneratedClass specificParser = new GeneratedClass("Parser", Visibility.Public);
    
    GeneratedMethod createOps = new GeneratedMethod("createOptions", "void", Visibility.Public);
    specificParser.addMethod(createOps);
    
    createOps.addStatement(new GeneratedStatement("Option op1 = new BooleanOption(\"a\")"));
    
    specificParser.addMethod(new GeneratedConstructor("Parser", Visibility.Public));
    
    new GeneratedCodePrinter(System.out).printClass(specificParser);
    
    //Method optionMethod = specificParser.addMethod("createOptions", "", "Options");
    
    //etc.
    
  }
  
  public static void main(String[] args) {
    createCode(null, null);
  }
  
}
