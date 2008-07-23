import java.util.*;

public abstract class OptionOverride implements IOverride {
    private final String explanation;
    
    public OptionOverride(String explanation) {
        this.explanation = explanation;
    }

    abstract public Boolean getOverride(OptVals vals, Option opt);

    public static OptionOverride and(String explanation, final IOverride[] overrides) {
        return new OptionOverride(explanation) {
            final IOverride[] os = overrides;
            public Boolean getOverride(OptVals vals, Option opt) {
                Boolean retv = null;
                for (int i = 0; i < os.length; i++) {
                    Boolean override = os[i].getOverride(vals, opt);
                    if (override != null) {
                        assert retv == null || retv.equals(override);
                        retv = override;
                    }
                }
                return retv;
            }
        };
    }

}
