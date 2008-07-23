import java.util.*;

abstract class Dependency {
    abstract public boolean isValid(Map<Option, Boolean> vals);

    public static Dependency and(final Iterable<Dependency> dependencies) {
        return new Dependency() {
            final Iterable<Dependency> ds = dependencies;
            public boolean isValid(Map<Option, Boolean> vals) {
                for (Dependency d : ds) {
                    if (!d.isValid(vals)) return false;
                }
                return true;
            }
        };
    }
}