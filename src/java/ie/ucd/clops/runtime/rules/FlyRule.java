package ie.ucd.clops.runtime.rules;


public class FlyRule extends Rule {

  private final String opId;
  
  public FlyRule(String opID, Expression<Boolean> condition) {
    super(getTrigger(opID), condition);
    this.opId = opID;
  }
  
  private static Trigger getTrigger(String opId) {
    //TODO real trigger
    return null;
  }

  @Override
  public String toString() {
    return "Fly rule affecting " + opId;
  }
}
