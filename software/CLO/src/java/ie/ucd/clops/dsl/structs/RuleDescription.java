package ie.ucd.clops.dsl.structs;

import ie.ucd.clops.logging.CLOLogger;

import java.util.LinkedList;
import java.util.List;
import java.util.logging.Level;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

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

  public void processPlaceHolders(DSLInformation dslInfo) {
    conditionText = processPlaceholders(conditionText, dslInfo);
    for (AssignmentDescription assignment : assignments) {
      assignment.processPlaceholders(dslInfo);
    }
  }
  
  private static final Pattern PLACEHOLDER_PATTERN = Pattern.compile("\\$\\([^\\(\\$\\)]+\\)");
  public static String processPlaceholders(String string, DSLInformation dslInfo) {
    if (string == null) return null;
    
    Matcher matcher = PLACEHOLDER_PATTERN.matcher(string);
    StringBuilder sb = new StringBuilder(string);
    int index = 0;
    int offset = 0;
    while (!matcher.hitEnd() && matcher.find(index)) {
      String match = matcher.group();
      String converted = convertMatch(match, dslInfo);
      sb.replace(matcher.start() + offset, matcher.end() + offset, converted);
      offset += converted.length() - match.length();
      index = matcher.end();
    }   
    return sb.toString();
  }
  
  private static final String convertMatch(String s, DSLInformation dslInfo) {
    s = s.trim();
    s = s.substring(2, s.length()-1);
    if (isIsSetPlaceholder(s)) {
      return convertIsSetPlaceholder(s.substring(0, s.length()-1), dslInfo);
    } else {
      return convertNormalPlaceholder(s, dslInfo);
    }
  }
  
  private static boolean isIsSetPlaceholder(String s) {
    return s.charAt(s.length()-1) == '?';
  }
  
  private static String convertNormalPlaceholder(String s, DSLInformation dslInfo) {
    OptionDescription desc = dslInfo.getOptionDescriptionForIdentifier(s);
    if (desc == null) {
      CLOLogger.getLogger().log(Level.SEVERE, "Unknown option identifier used in placeholder: " + s);
      return "";
    } else {
      return "((" + desc.getType().getOptionTypeClass() + ")optionStore.getOptionByIdentifier(\"" + desc.getIdentifier() + "\")).getValue()";
    }
  }
  
  private static String convertIsSetPlaceholder(String s, DSLInformation dslInfo) {
    OptionDescription desc = dslInfo.getOptionDescriptionForIdentifier(s);
    if (desc == null) {
      CLOLogger.getLogger().log(Level.SEVERE, "Unknown option identifier used in placeholder: " + s);
      return "";
    } else {
      return "((" + desc.getType().getOptionTypeClass() + ")optionStore.getOptionByIdentifier(\"" + desc.getIdentifier() + "\")).hasValue()";
    }
  }
}
