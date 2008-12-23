package ie.ucd.clops.dsl.structs;

import java.util.LinkedList;
import java.util.List;

/**
 * 
 * @author Fintan
 *
 */
public class RuleDescription {

  private static int count = 1;
  
  protected final List<AssignmentDescription> assignments;
  private String conditionText;
  private final String id;

  public RuleDescription() {
    this.assignments = new LinkedList<AssignmentDescription>();
    this.id = (count++) + "";
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

  public String getId() {
    return id;
  }

}
