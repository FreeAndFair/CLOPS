package ie.ucd.clops.dsl.structs;

import java.util.regex.Matcher;
import java.util.regex.Pattern;

/**
 * 
 * @author Fintan
 *
 */
public class ValidityRuleDescription extends RuleDescription {

  private String explanation;

  public String getExplanation() {
    return explanation;
  }

  public void setExplanation(String explanation) {
    this.explanation = explanation;
  }

  public static ValidityRuleDescription fromRequires(String opName, String requiresExpression) {
    StringBuilder sb = new StringBuilder();
    sb.append("$(");
    sb.append(opName);
    sb.append("?) ? !");
    sb.append(convertNamesToIsSetPlaceholders(requiresExpression).trim());
    sb.append(" : false");
    ValidityRuleDescription rule = new ValidityRuleDescription();
    rule.setConditionText(sb.toString());
    return rule;
  }
  
  private static final Pattern NAME_PATTERN = Pattern.compile("[A-Za-z][A-Za-z0-9_-]*");  
  private static String convertNamesToIsSetPlaceholders(String requires) {
    Matcher matcher = NAME_PATTERN.matcher(requires);
    StringBuilder sb = new StringBuilder(requires);
    int index = 0;
    int offset = 0;
    while (!matcher.hitEnd() && matcher.find(index)) {
      String match = matcher.group();
      String converted = "$(" + match + "?)";
      sb.replace(matcher.start() + offset, matcher.end() + offset, converted);
      offset += converted.length() - match.length();
      index = matcher.end();
    }   
    return sb.toString();
  }
  
}
