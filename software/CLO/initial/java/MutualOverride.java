import java.util.HashSet;
import java.util.Set;

/**
 * 
 */

public class MutualOverride implements IOverride {
    Set<Option> os;
    MutualOverride(Option[] os) {
        this.os = new HashSet<Option>();
        for (int i = 0; i < os.length; i++) { 
            assert !this.os.contains(os[i]);
            this.os.add(os[i]);
        }
    }

    public Boolean getOverride(OptVals vals, Option opt) {
        if (!os.contains(opt)) return null;
        for (Option o : os) {
            if (opt.equals(o)) continue;
            if (vals.isTrue(o) && vals.before(opt, o)) { 
                System.out.println(o + " knocking down " + opt);
                return false;
            }
        }
        return null;
    }
}