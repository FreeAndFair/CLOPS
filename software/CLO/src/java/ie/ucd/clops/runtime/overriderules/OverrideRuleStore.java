package ie.ucd.clops.runtime.overriderules;

import ie.ucd.clops.runtime.options.Option;
import ie.ucd.clops.runtime.options.OptionAssignment;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

/**
 * 
 * @author Fintan
 *
 */
public class OverrideRuleStore {

  private final Map<String,Collection<OptionAssignment>> optionIdentifierToAssignmentMap;

  public OverrideRuleStore() {
    this.optionIdentifierToAssignmentMap = new HashMap<String,Collection<OptionAssignment>>();
  }
  
  public void addAssignmentForOption(String optionIdentifier, OptionAssignment assignment) {
    Collection<OptionAssignment> existingAssignments = optionIdentifierToAssignmentMap.get(optionIdentifier);
    if (assignment == null) {
      existingAssignments = new LinkedList<OptionAssignment>();
    }
    existingAssignments.add(assignment);
  }

  public Collection<OptionAssignment> getAssignmentsForOption(String optionIdentifier) {
    return optionIdentifierToAssignmentMap.get(optionIdentifier);
  }

  public Collection<OptionAssignment> getAssignmentsForOption(Option option) {
    return getAssignmentsForOption(option.getIdentifier());
  }
  
}
