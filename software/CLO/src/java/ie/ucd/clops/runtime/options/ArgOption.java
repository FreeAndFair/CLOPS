package ie.ucd.clops.runtime.options;

import java.util.*;
import java.util.regex.*;

import ie.ucd.clops.runtime.parser.ProcessingResult;

/**
 * This class represents an argument option. 
 * An option whose value is the string on which it matched.
 *
 * @author Mikolas Janota
 *
 */
public class ArgOption implements Option<String> {
    private Pattern form;
    private String val = null;
    private final String identifier;

    /** 
     * Construct a new {@code ArgOption}.
     * @param regexStr a regular expression {@link java.util.regex.Pattern}
     */
    public ArgOption(String identifier, String regexStr) {
        this.identifier = identifier;
        this.form = Pattern.compile(regexStr);
    }

    public String getIdentifier() { return identifier; }

    public Option<?> getMatchingOption(String argument) {
        return matches(argument) ? this : null;
    }  

    public ProcessingResult process(/*@non_null*/String[] args, int offset) {
        String argument = args[offset];
        assert getMatchingOption(argument) == this;
        this.val = argument;
        return new ProcessingResult(1, false, null);
    }


    public /*@pure*/boolean hasValue() { return val == null; }
  
    public /*@pure*/String getValue() { return val; }
  
    public void unset() { val = null; }
  
    public void set(Object value) throws InvalidOptionValueException {
    }

    public void setFromString(String value) throws InvalidOptionValueException {
        if (!matches(value)) {
            String msg = "The given string (\"" + value + "\") does not correspond to the format of this argument";
            throw new InvalidOptionValueException(msg);
        }
        this.val = value;
    }
  
    public void addAlias(String alias) {
        assert false;
        //TODO
    }

    public Set<String> getAliases() {
        assert false;
        //TODO
        return null;
    }
  
    public void setProperty(/*@non_null*/String propertyName, String propertyValue) 
       throws InvalidOptionPropertyValueException {
        throw new InvalidOptionPropertyValueException("");
    }
  
    public /*@pure*/boolean acceptsProperty(/*@non_null*/String propertyName) {
        return false;
    }


    /**
     * Determines whether the given string matches this argument. 
     */
    private boolean matches(String s) {
        Matcher m = form.matcher(s);
        return m.matches();
    }
  

}
