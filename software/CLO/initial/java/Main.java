import java.util.*;

public class Main {

    public static void main(String[] args) {
        List<Option> opts = new ArrayList<Option>(args.length);
        LSDefs lsDef = new LSDefs();

        // convert strings to options
        for (int i = 0; i < args.length; i++) {
            Option o = Option.findOption(args[i]);
            if (o == null) {
                System.out.println(args[i] + " unknown");
                System.exit(1);
            }
            opts.add(o);
        }

        // fixpoint computation for overrides
        OptVals optVals = new OptVals(opts);
        OptVals oldVals;
        do {
            oldVals = new OptVals(optVals);

            assert lsDef.isValid(optVals);

            for (Option o : Option.getOptions()) {
                Boolean ov = lsDef.getOverride(optVals, o);
                if (ov != null) {
                    System.out.println("overriding " + o + " with " + ov);
                    optVals.set(o, ov);
                }
            }
        } while (!oldVals.equals(optVals));


        System.out.println("opts: " + opts);
    }

}
