
public class MutuallyExclusiveConstraint implements IConstraint {

  private final Option op1;
  private final Option op2;
  
  public MutuallyExclusiveConstraint(String op1name, String op2name) {
    op1 = Option.findOption(op1name);
    op2 = Option.findOption(op2name);
    
    assert op1 != null && op2 != null;
  }
  
  public boolean isValid(OptVals vals) {
    return !(vals.isTrue(op1) && vals.isTrue(op2));
  }

}
