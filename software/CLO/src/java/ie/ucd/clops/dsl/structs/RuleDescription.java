package ie.ucd.clops.dsl.structs;

import java.util.LinkedList;
import java.util.List;

/**
 * 
 * @author Fintan
 *
 */
public class RuleDescription {

  protected final List<AssignmentDescription> assignments;
  private String conditionText;

  public RuleDescription() {
    this.assignments = new LinkedList<AssignmentDescription>();
  }
  
  public void addAssignment(AssignmentDescription assign) {
    this.assignments.add(assign);
  }

  public List<AssignmentDescription> getAssignments() {
    return assignments;
  }

  public String getConditionText() {
    return conditionText;
  }

  public void setConditionText(String conditionText) {
    this.conditionText = conditionText;
  }

}
