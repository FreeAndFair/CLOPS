package ie.ucd.clops.codegeneration;

import ie.ucd.clops.codegeneration.GeneratedCodeUnit.Visibility;

import java.io.PrintStream;
import java.util.List;

public class GeneratedCodePrinter {

  private int indentationLevel;
  private PrintStream ps;

  private static int SPACES_PER_INDENT = 2;

  public GeneratedCodePrinter(PrintStream ps) {
    indentationLevel = 0;
    this.ps = ps;
  }

  public void reset(PrintStream ps) {
    indentationLevel = 0;
    this.ps = ps;
  }

  public void indent() {
    indentationLevel++;
  }

  public void dedent() {
    indentationLevel--;
  }

  public void newLine() {
    ps.println();
    startLine();
  }

  private final void startLine() {
    int numSpaces = indentationLevel * SPACES_PER_INDENT; 
    for (int i=0; i < numSpaces; i++) {
      space();
    }
  }

  private final void space() {
    ps.print(' ');
  }
  
  private final void openBraces() {
    ps.print('{');
    indent();
    newLine();
  }
  
  private final void closeBraces() {
    dedent();
    newLine();
    ps.print('}');
    newLine();
  }

  public void printClass(GeneratedClass genClass) {
    startLine();

    printVisibility(genClass.getVisibility());
    printModifiers(genClass.getModifiers());
    ps.print(genClass.getName());
    space();
    
    openBraces();
    
    for (GeneratedField field : genClass.getFields()) {
      printField(field);
    }
    
    for (GeneratedMethod method : genClass.getMethods()) {
      printMethod(method);
    }
    
    closeBraces();    
  }
  
  public void printField(GeneratedField field) {
    printVisibility(field.getVisibility());
    printModifiers(field.getModifiers());
    ps.print(field.getType());
    space();
    ps.print(field.getName());
    space();
  }
  
  public void printMethod(GeneratedMethod method) {
    printVisibility(method.getVisibility());
    printModifiers(method.getModifiers());
    if (!(method instanceof GeneratedConstructor)) {
      ps.print(method.getReturnType());
      space();
    }
        
    ps.print(method.getName());
    ps.print('(');
    printArguments(method.getArgs());
    ps.print(')');
    
    space();    
    openBraces();
    
    for (GeneratedStatement statement : method.getStatements()) {
      printStatement(statement);
    }    
    
    closeBraces();
  }
  
  private final void printArguments(List<GeneratedArgument> args) {
    if (args.size() > 0) {
      printArgument(args.get(0));      
      
      for (int i=1; i < args.size(); i++) {
        ps.print(", ");
        printArgument(args.get(i));
      }
      
    }
  }
  
  private final void printArgument(GeneratedArgument arg) {
    ps.print(arg.getArgumentType());
    space();
    ps.print(arg.getArgumentName());
  }
  
  public void printStatement(GeneratedStatement statement) {
    ps.print(statement.getContent());
    ps.print(';');
    newLine();
  }
  

  private final void printVisibility(Visibility vis) {
    switch(vis) {
    case Private:
      ps.print("private ");
      break;
    case Protected:
      ps.print("protected ");
      break;
    case PackagePrivate:
      break;
    case Public:
      ps.print("public ");
      break;
    }
  }
  
  private final void printModifiers(List<String> mods) {
    for (String mod : mods) {
      ps.print(mod);
      space();
    }
  }

  

}
