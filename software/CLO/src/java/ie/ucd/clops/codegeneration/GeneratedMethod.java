package ie.ucd.clops.codegeneration;

import java.util.LinkedList;
import java.util.List;

public class GeneratedMethod extends GeneratedCodeUnit {

  private final List<GeneratedArgument> args;
  private final List<GeneratedStatement> statements;
  private final List<String> exceptions;
  private boolean isAbstract;
  private final String returnType;
  
  public GeneratedMethod(String name, String returnType, Visibility visibility) {
    super(name, visibility);
    this.returnType = returnType;
    this.args = new LinkedList<GeneratedArgument>();
    this.statements = new LinkedList<GeneratedStatement>();
    this.exceptions = new LinkedList<String>();
    isAbstract = false;
  }

  public GeneratedMethod(String name, String returnType) {
    super(name);
    this.returnType = returnType;
    this.args = new LinkedList<GeneratedArgument>();
    this.statements = new LinkedList<GeneratedStatement>();
    this.exceptions = new LinkedList<String>();
    isAbstract = false;
  }

  public void addArg(GeneratedArgument arg) {
    args.add(arg);
  }
  
  public void addStatement(GeneratedStatement statement) {
    statements.add(statement);
  }
  
  public void addStatement(String statementText) {
    statements.add(new GeneratedStatement(statementText));
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

  public boolean isAbstract() {
    return isAbstract;
  }

  public void setAbstract(boolean isAbstract) {
    this.isAbstract = isAbstract;
  }

  public void addException(String exceptionName) {
    exceptions.add(exceptionName);
  }
  
  public List<String> getExceptions() {
    return exceptions;
  }
  
}
