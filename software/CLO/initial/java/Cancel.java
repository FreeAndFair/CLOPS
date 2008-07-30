/**
 * 
 */

public class Cancel extends OptionOverride {
    Option o, toCancel;
    Cancel(String explanation, Option o, Option toCancel) {
        super(explanation);
        this.o = o; 
        this.toCancel = toCancel;
    }
    public Boolean getOverride(OptVals vals, Option opt) {
        if (!opt.equals(toCancel)) return null;
        if (vals.isTrue(o)) return false;
        return null;
    }
}