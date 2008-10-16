package ie.ucd.clops.codegeneration.java;

import java.util.LinkedList;
import java.util.List;

public class GeneratedMethod extends GeneratedCodeUnit {

  private final List<GeneratedArgument> args;
  private final List<GeneratedStatement> statements;
  private final String returnType;
  
  public GeneratedMethod(String name, String returnType, Visibility visibility) {
    super(name, visibility);
    this.returnType = returnType;
    this.args = new LinkedList<GeneratedArgument>();
    this.statements = new LinkedList<GeneratedStatement>();
  }

  public GeneratedMethod(String name, String returnType) {
    super(name);
    this.returnType = returnType;
    this.args = new LinkedList<GeneratedArgument>();
    this.statements = new LinkedList<GeneratedStatement>();
  }

  public void addArg(GeneratedArgument arg) {
    args.add(arg);
  }
  
  public void addStatement(GeneratedStatement statement) {
    statements.add(statement);
  }
  
  public List<GeneratedArgument> getArgs() {
    return args;
  }
  
  public List<GeneratedStatement> getStatements() {
    return statements;
  }

  public String getReturnType() {
    return returnType;
  }  

}
