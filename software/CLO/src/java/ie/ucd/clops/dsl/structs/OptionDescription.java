package ie.ucd.clops.dsl.structs;

import java.util.*;

public class OptionDescription {
    private /*@non_null*/Set<String> aliases;
    private /*@non_null*/OptionType type;

    public OptionType getType() { return type; }

    /**
     * Determines whether the given string is an alias of this option description.
     */
    public boolean isAlias(String alias) { return aliases.contains(alias); }
}