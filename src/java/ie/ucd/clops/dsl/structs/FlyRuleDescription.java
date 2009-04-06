package ie.ucd.clops.dsl.structs;

/**
 * 
 * @author Fintan
 *
 */
public class FlyRuleDescription extends RuleDescription {

  private final String triggeringOptionIdentifier;
  public FlyRuleDescription(String triggeringOptionIdentifier) {
    this.triggeringOptionIdentifier = triggeringOptionIdentifier;
  }

  public String getTriggeringOptionIdentifier() {
    return triggeringOptionIdentifier;
  }
    
}
