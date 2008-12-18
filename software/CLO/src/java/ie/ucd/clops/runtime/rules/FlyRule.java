package ie.ucd.clops.runtime.rules;


public class FlyRule extends Rule {

  public FlyRule(String opID, Expression<Boolean> condition) {
    super(getTrigger(opID), condition);
  }
  
  private static Trigger getTrigger(String opId) {
    //TODO real trigger
    return null;
  }
  
}
