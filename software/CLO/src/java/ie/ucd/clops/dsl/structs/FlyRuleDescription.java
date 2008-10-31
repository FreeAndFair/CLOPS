package ie.ucd.clops.dsl.structs;

import java.util.Collection;
import java.util.LinkedList;

/**
 * 
 * @author Fintan
 *
 */
public class FlyRuleDescription {

  private final String triggeringOptionIdentifier;
  private final Collection<AssignmentDescription> assignments;
  
  public FlyRuleDescription(String triggeringOptionIdentifier) {
    this.assignments = new LinkedList<AssignmentDescription>();
    this.triggeringOptionIdentifier = triggeringOptionIdentifier;
  }

  public void addAssignment(AssignmentDescription assign) {
    this.assignments.add(assign);
  }
  
  public String getTriggeringOptionIdentifier() {
    return triggeringOptionIdentifier;
  }

  public Collection<AssignmentDescription> getAssignments() {
    return assignments;
  }
  
}