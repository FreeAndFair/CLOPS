package ie.ucd.clops.runtime.options;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.regex.Matcher;
import java.util.regex.Pattern;

import ie.ucd.clops.runtime.options.exception.InvalidOptionPropertyValueException;
import ie.ucd.clops.runtime.options.exception.InvalidOptionValueException;
import ie.ucd.clops.util.Pair;
import ie.ucd.clops.util.StringUtil;

/**
 * 
 * An option whose value is one of a given finite set of strings.
 * These string are given in the property "choices" and the value is a
 * comma-separated list of the individual values. The spaces are
 * preserved
 * @author Fintan
 *
 */
public class EnumOption extends StringOption implements IEnumOption {

  private final EnumPart enumPart;

  public EnumOption(String identifier, String prefix) {
    super(identifier, prefix);
    enumPart = new EnumPart();
  }

  @Override
  public void set(String value) throws InvalidOptionValueException {
    if (enumPart.isValidValue(value)) {
      super.set(value);
    } else {
      throw new InvalidOptionValueException(value + " is not an allowed choice.");
    }
  }

  //Static for space/time efficiency (we don't need one per instance) 
  private static Collection<String> acceptedPropertyNames; 
  protected static Collection<String> getStaticAcceptedPropertyNames() {
    if (acceptedPropertyNames == null) {
      acceptedPropertyNames = new ArrayList<String>();  
      acceptedPropertyNames.addAll(StringOption.getStaticAcceptedPropertyNames());
      acceptedPropertyNames.addAll(EnumPart.getStaticAcceptedPropertyNames());
    }
    return acceptedPropertyNames;
  }

  @Override
  public Collection<String> getAcceptedPropertyNames() {
    return getStaticAcceptedPropertyNames();
  }

  @Override
  public void setProperty(String propertyName, String propertyValue)
  throws InvalidOptionPropertyValueException {
    if (!enumPart.setProperty(propertyName, propertyValue)) {
      super.setProperty(propertyName, propertyValue);
    }
  }

  public EnumPart getEnumPart() {
    return enumPart;
  }

  @Override
  protected String getTypeString() {
    return "StringEnum";
  } 

  public static class EnumPart {

    private final List<String> choices;
    private boolean caseSensitive;

    public EnumPart() {
      choices = new ArrayList<String>();
      caseSensitive = false;
    }

    public void addChoice(String choice) {
      choices.add(choice);
    }

    public boolean isValidValue(String value) {
      return isValidValue(value, choices, caseSensitive);
    }

    public static boolean isValidValue(String value, Iterable<String> choices, boolean caseSensitive) {
      for (String choice : choices) {
        if ((caseSensitive && choice.equals(value)) || 
            choice.equalsIgnoreCase(value)) {
          return true;
        }
      }
      return false;
    }

    //Static for space/time efficiency (we don't need one per instance) 
    private static Collection<String> acceptedPropertyNames; 
    protected static Collection<String> getStaticAcceptedPropertyNames() {
      if (acceptedPropertyNames == null) {
        acceptedPropertyNames = new ArrayList<String>();  
        acceptedPropertyNames.addAll(StringOption.getStaticAcceptedPropertyNames());
        acceptedPropertyNames.add("choices");
        acceptedPropertyNames.add("casesensitive");
      }
      return acceptedPropertyNames;
    }

    public Collection<String> getAcceptedPropertyNames() {
      return getStaticAcceptedPropertyNames();
    }

    public boolean setProperty(String propertyName, String propertyValue)
    throws InvalidOptionPropertyValueException {

      if (propertyName.equalsIgnoreCase("choices")) {
        List<Pair<String, List<String>>> pc = parseChoices(propertyValue);
        for (Pair<String, List<String>> c : pc) {
          for (String cs : c.getSecond()) {
            choices.add(cs);
          }
        }
        if (pc.isEmpty()) {
          throw new InvalidOptionPropertyValueException(
              "Enums must have at least one value.");
        }
        return true;
      } else if (propertyName.equalsIgnoreCase("casesensitive")) {
        caseSensitive = Options.parseBooleanProperty(propertyName, propertyValue);
        return true;
      } else {
        return false;
      }
    }
  }

  public static List<Pair<String, List<String>>> parseChoices(String choice) {
    final List<Pair<String, List<String>>> r = 
      new ArrayList<Pair<String, List<String>>>();
    if (choice == null || choice.isEmpty()) {
      return r;
    }
    for (String part : StringUtil.mkList(choice)) {
      parseChoicePart(part, r);
    }
    return check(r);
  }
  
  private static void parseChoicePart(String part, List<Pair<String, List<String>>> r) {
    String name, parseStrings;
    final int index = part.indexOf('(');
    if (index != -1) {
      if (part.charAt(part.length() - 1) != ')') {
        throw new InvalidOptionPropertyValueException(
            "The enum specification <" + part + "> should end with ')'.");
      }
      parseStrings = part.substring(0, index);
      name = part.substring(index + 1, part.length() - 1);
    } else {
      parseStrings = part;
      name = part;
    }
    r.add(Pair.mk(name, StringUtil.mkList(parseStrings, "\\|")));
  }

  private static List<Pair<String, List<String>>> check(
      final List<Pair<String, List<String>>> choices) {
    HashSet<String> values = new HashSet<String>();
    HashSet<String> strings = new HashSet<String>();
    for (Pair<String, List<String>> p : choices) {
      check(p.getFirst(), values, "values");
      checkId(p.getFirst());
      for (String s : p.getSecond()) {
        check(s, strings, "strings");
      }
    }
    return choices;
  }

  private static final Pattern specialCharacters = 
      Pattern.compile("[\\(\\)\\|]");

  private static void check(String s, Set<String> set, String c) {
    if (set.contains(s)) {
      throw new InvalidOptionPropertyValueException(
          "Enum " + c + " should be unique: " + s);
    }
    if (s.equals("")) {
      throw new InvalidOptionPropertyValueException(
          "Enum " + c + " can't be empty.");
    }
    Matcher m = specialCharacters.matcher(s);
    if (specialCharacters.matcher(s).find()) {
      throw new InvalidOptionPropertyValueException(
          "The format for the 'choices' property is " +
          "\"valueA,stringB(valueB),stringCA|stringCB(valueC)\".");
    }
    set.add(s);
  }

  private static final void checkId(String id) {
    if (!StringUtil.isJavaId(id)) {
      throw new InvalidOptionPropertyValueException(
        "\"" + id + "\" is not a nice Java identifier.");
    }
  }
}


