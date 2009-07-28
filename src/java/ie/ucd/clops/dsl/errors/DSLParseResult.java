package ie.ucd.clops.dsl.errors;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.List;
import java.util.SortedSet;
import java.util.TreeSet;

public class DSLParseResult {

  private static final long serialVersionUID = -3669680674888999650L;

  private final List<DSLError> errors;
  private final List<DSLWarning> warnings;
  
  public DSLParseResult() {
    errors = new ArrayList<DSLError>();
    warnings = new ArrayList<DSLWarning>();
  }
  
  public void addAll(DSLParseResult other) {
    errors.addAll(other.errors);
    warnings.addAll(other.warnings);
  }
  
  public void addError(DSLError error) {
    errors.add(error);
  }
  
  public void addWarning(DSLWarning warning) {
    warnings.add(warning);
  }
  
  public void printToStream(PrintStream ps) {
    
    if (!errors.isEmpty() || !warnings.isEmpty()) {
      SortedSet<DSLProblem> allProblems = new TreeSet<DSLProblem>();
      allProblems.addAll(errors);
      allProblems.addAll(warnings);

      for (DSLProblem error : allProblems) {
        error.printToStream(ps);
      }
      printSummary(ps);
    }
  }
  
  private void printSummary(PrintStream ps) {
    if (!errors.isEmpty()) {
      ps.println(errors.size() + " error" + (errors.size() > 1 ? "s." : "."));
    }
    if (!warnings.isEmpty()) {
      ps.println(warnings.size() + " warning" + (warnings.size() > 1 ? "s." : "."));
    }
  }
  
  public boolean successfulParse() {
    return errors.isEmpty();
  }
}
