package ie.ucd.clops.runtime.errors;

import java.io.PrintStream;
import java.util.SortedSet;
import java.util.TreeSet;

public class ParseResult {

  private final String commandLineInput;
  private final SortedSet<CLProblem> errors;
  private final SortedSet<CLProblem> warnings;
  private final SortedSet<CLProblem> combined;
  
  public ParseResult(String commandLineInput) {
    this.commandLineInput = commandLineInput;
    errors = new TreeSet<CLProblem>();
    warnings = new TreeSet<CLProblem>();
    combined = new TreeSet<CLProblem>();
  }
  
  public ParseResult() {
    this((String)null);
  }
  
  public ParseResult(ParseResult toClone) {
    this.commandLineInput = toClone.commandLineInput;
    this.errors = new TreeSet<CLProblem>(toClone.errors);
    this.warnings = new TreeSet<CLProblem>(toClone.warnings);
    this.combined = new TreeSet<CLProblem>(toClone.combined);
  }
  
  public void addError(CLError error) {
    errors.add(error);
    combined.add(error);
  }
  
  public void addWarning(CLWarning warning) {
    warnings.add(warning);
    combined.add(warning);
  }
  
  public void addAll(ParseResult result) {
    for (CLProblem error : result.errors) {
      errors.add(error);
      combined.add(error);
    }
    for (CLProblem warning : result.warnings) {
      warnings.add(warning);
      combined.add(warning);
    }
  }
  
  public boolean successfulParse() {
    return errors.isEmpty();
  }

  public SortedSet<CLProblem> getErrors() {
    return errors;
  }

  public SortedSet<CLProblem> getWarnings() {
    return warnings;
  }

  public SortedSet<CLProblem> getErrorsAndWarnings() {
    return combined;
  }
  
  public void printErrorsAndWarnings(PrintStream ps) {
    print(combined, ps);
  }
  
  public void printErrors(PrintStream ps) {
    print(errors, ps);
  }
  
  public void printWarnings(PrintStream ps) {
    print(warnings, ps);
  }
  
  private void print(SortedSet<CLProblem> problems, PrintStream ps) {
    for (CLProblem problem : problems) {
      problem.printToStream(ps, commandLineInput);
    }
  }

}
