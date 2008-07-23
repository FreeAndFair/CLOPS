import java.util.*;

/**
 * Description of the ls options.
 *
 * @author Mikolas Janota
 */
public class LSDefs implements IOptionDefs {
    private Option optH = Option.registerOption("-h");
    private Option optP = Option.registerOption("-P");
    private Option optL = Option.registerOption("-L");
    private Option optF = Option.registerOption("-F");
    private Option optd = Option.registerOption("-d");
    private Option optl = Option.registerOption("-l");
    private Option opt1 = Option.registerOption("-1");
    private Option optx = Option.registerOption("-x");
    private Option optC = Option.registerOption("-C");
    private Option optc = Option.registerOption("-c");
    private Option optu = Option.registerOption("-u");
    private Option optb = Option.registerOption("-b");
    private Option optB = Option.registerOption("-B");
    private Option optw = Option.registerOption("-w");
    private Option optq = Option.registerOption("-q");

    private OptionDefaults HDef = 
        new OptionDefaults("Links are treated with -H option if none of -F, -d, and -l are specified") {
            public Boolean getDefault(OptVals vals, Option opt) {
                if (!opt.equals(optH)) return null;
                if (vals.isFalse(optF) && vals.isFalse(optd) && vals.isFalse(optl)) 
                    return true;
                else return null;
            }
        };

    private OptionOverride LOverrideP = new Cancel("-L cancels -P", optL, optP);
    private OptionOverride POverrideH = new Cancel("-P cancels -H", optP, optH);
    private OptionOverride POverrideL = new Cancel("-P cancels -L", optP, optL);
    private MutualOverride listings = new MutualOverride(new Option[] { opt1, optC, optx, optl } );
    private MutualOverride fileTime = new MutualOverride(new Option[] { optc, optu });
    private MutualOverride nonprintableChars = new MutualOverride(new Option[] { optB, optb, optw, optq });

    /** The overall override function for ls */
    OptionOverride totalOverride = OptionOverride.and("ls overrides", new IOverride[] 
        { LOverrideP, POverrideH, POverrideL, listings, fileTime, nonprintableChars });

    /** Implementation of the {@code IDefault} interface. */
    public Boolean getDefault(OptVals vals, Option opt) {
        return HDef.getDefault(vals, opt);
    }

    /** Implementation of the {@code IOverride} interface. */
    public Boolean getOverride(OptVals vals, Option opt) {
        return totalOverride.getOverride(vals, opt);
    }

    /** Implementation of the {@code IConstraint} interface. */
    public boolean isValid(OptVals vals) {
        return true;
    }

    private class Cancel extends OptionOverride {
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

    class MutualOverride implements IOverride {
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
}