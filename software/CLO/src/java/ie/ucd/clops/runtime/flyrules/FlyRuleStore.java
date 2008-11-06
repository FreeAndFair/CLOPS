package ie.ucd.clops.runtime.flyrules;

import ie.ucd.clops.runtime.options.InvalidOptionValueException;
import ie.ucd.clops.runtime.options.Option;
import ie.ucd.clops.runtime.options.OptionAssignment;
import ie.ucd.clops.runtime.options.OptionStore;

import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.Map;

/**
 * 
 * @author Fintan
 *
 */
public class FlyRuleStore {

  private final Map<String,Collection<OptionAssignment>> optionIdentifierToAssignmentMap;

  public FlyRuleStore() {
    this.optionIdentifierToAssignmentMap = new HashMap<String,Collection<OptionAssignment>>();
  }
  
  public void addAssignmentForOption(String optionIdentifier, OptionAssignment assignment) {
    Collection<OptionAssignment> existingAssignments = optionIdentifierToAssignmentMap.get(optionIdentifier);
    if (existingAssignments == null) {
      existingAssignments = new LinkedList<OptionAssignment>();
      optionIdentifierToAssignmentMap.put(optionIdentifier, existingAssignments);
    }
    existingAssignments.add(assignment);
    System.out.println("Added assignment " + assignment + " for " + optionIdentifier);
  }

  public Collection<OptionAssignment> getAssignmentsForOption(String optionIdentifier) {
    return optionIdentifierToAssignmentMap.get(optionIdentifier);
  }

  public Collection<OptionAssignment> getAssignmentsForOption(Option option) {
    return getAssignmentsForOption(option.getIdentifier());
  }
  
  public void applyFlyRules(Option matchedOption, OptionStore optionStore) throws InvalidOptionValueException {
    Collection<OptionAssignment> assignments = getAssignmentsForOption(matchedOption);
    if (assignments != null) {
      System.out.println("Assignments for " + matchedOption);
      for (OptionAssignment assignment : assignments) {
        Option optionToSet = optionStore.getOptionByIdentifier(assignment.getOptionIdentifier());
        optionToSet.setFromString(assignment.getOptionValue());
      }          
    }
  }

  @Override
  public String toString() {
    StringBuilder sb = new StringBuilder();
    sb.append("Fly rule store contents:\n");
    
    for (String opId : optionIdentifierToAssignmentMap.keySet()) {
      sb.append(opId + " - ");
      Collection<OptionAssignment> assignments = optionIdentifierToAssignmentMap.get(opId);
      for (OptionAssignment assignment : assignments) {
        sb.append(assignment.toString());
        sb.append(", ");
      }
      sb.append('\n');
    }
    
    return sb.toString();
  }  
  
}
