
public class BooleanDefault implements IDefault {

  private final String[] requiredTrue;
  private final String[] requiredFalse;
  private final Boolean defaultVal;
  
  public BooleanDefault(String[] requiredTrue, String[] requiredFalse, Boolean defaultVal) {
    this.requiredTrue = requiredTrue;
    this.requiredFalse = requiredFalse;
    this.defaultVal = defaultVal;
  }

  public Boolean getDefault(OptVals vals, Option opt) {
    for (String s : requiredTrue) {
      if (!vals.isTrue(Option.findOption(s))) {
        return null;
      }
    }
    for (String s : requiredFalse) {
      if (!vals.isFalse(Option.findOption(s))) {
        return null;
      }
    }
    return defaultVal;
  }

}
