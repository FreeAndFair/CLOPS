package ie.ucd.clops.dsl;

import ie.ucd.clops.dsl.errors.DSLParseResult;
import ie.ucd.clops.dsl.errors.DuplicateOptionIdentifier;
import ie.ucd.clops.dsl.errors.MissingPropertyError;
import ie.ucd.clops.dsl.errors.PropertyValueError;
import ie.ucd.clops.dsl.errors.UnknownIdentifierError;
import ie.ucd.clops.dsl.errors.UnusedIdentifierWarning;
import ie.ucd.clops.dsl.structs.DSLInformation;
import ie.ucd.clops.dsl.structs.OptionDescription;
import ie.ucd.clops.dsl.structs.OptionGroupDescription;
import ie.ucd.clops.runtime.automaton.Token;
import ie.ucd.clops.runtime.automaton.Tokenizer;
import ie.ucd.clops.runtime.options.IEnumOption;
import ie.ucd.clops.runtime.options.IMatchString;
import ie.ucd.clops.runtime.options.IMatchable;
import ie.ucd.clops.runtime.options.Option;
import ie.ucd.clops.runtime.options.exception.InvalidOptionPropertyValueException;
import ie.ucd.clops.util.Pair;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

public class StaticChecker {

  private DSLInformation dslInfo;

  public StaticChecker(DSLInformation dslInfo) {
    this.dslInfo = dslInfo;
  }

  public DSLParseResult runAllChecks() {

    DSLParseResult errors = new DSLParseResult();

    errors.addAll(checkForDuplicateIdentifierUse());
    errors.addAll(checkForUnusedOptionsOrGroups());
    errors.addAll(checkProperties());
    
    return errors;
  }

  public DSLParseResult checkForDuplicateIdentifierUse() {
    DSLParseResult result = new DSLParseResult();
    //Duplicates within option identifiers or option group identifiers 
    //are already checked as we parse
    //So just check if we have overlaps between options and groups
    for (OptionDescription option : dslInfo.getOptionDescriptions()) {
      OptionGroupDescription other = dslInfo.getOptionGroupNameMap().get(option.getIdentifier());
      if (other != null) {
        result.addError(new DuplicateOptionIdentifier(other.getSourceLocation(), option.getIdentifier(), option.getSourceLocation()));
      }
    }

    return result;
  }

  public DSLParseResult checkForUnusedOptionsOrGroups() {
    DSLParseResult result = new DSLParseResult();

    String formatString = dslInfo.getFormatString();
    Set<String> identifiersUsedInFormatString = getUsedIdentifiers(formatString);
    Set<String> allUsedIdentifiers = expandUsedIdentifiers(identifiersUsedInFormatString);

    Set<String> allIdentifiers = dslInfo.getOptionAndGroupNameMap().keySet();


    Set<String> missingIdentifiers = new HashSet<String>(allUsedIdentifiers);
    missingIdentifiers.removeAll(allIdentifiers);
    for (String missing : missingIdentifiers) {
      //TODO more specific source locations for format string!
      if (!missing.equals("AllOptions")) {
        result.addError(new UnknownIdentifierError(dslInfo.getFormatSourceLocation(), missing));
      }
    }

    Set<String> unusedIdentifiers = new HashSet<String>(allIdentifiers);
    unusedIdentifiers.removeAll(allUsedIdentifiers);
    for (String unused : unusedIdentifiers) {
      OptionDescription unusedOption = dslInfo.getOptionNameMap().get(unused);
      if (unusedOption != null && !virtualOption(unusedOption)) {
        result.addWarning(new UnusedIdentifierWarning(dslInfo.getFormatSourceLocation(), dslInfo.getOptionNameMap().containsKey(unused), unused));
      }
    }    

    return result;
  }
  
  private static boolean virtualOption(OptionDescription option) {
    for (Pair<String,String> property : option.getProperties()) {
      if (property.getFirst().equalsIgnoreCase("virtual") && property.getSecond().equalsIgnoreCase("true")) {
        return true;
      }
    }
    return false;
  }

  private Set<String> expandUsedIdentifiers(Set<String> usedInFormat) {
    Set<String> toVisit = new HashSet<String>(usedInFormat);
    Set<String> visited = new HashSet<String>();

    while (!toVisit.isEmpty()) {
      toVisit.removeAll(visited);
      for (String newId : new HashSet<String>(toVisit)) {
        visited.add(newId);
        toVisit.remove(newId);
        if (newId.equals("AllOptions")) {
          toVisit.addAll(dslInfo.getOptionNameMap().keySet());
        } else {
          OptionGroupDescription group = dslInfo.getOptionGroupNameMap().get(newId);
          if (group != null) {
            Set<String> children = new HashSet<String>(group.getChildren());
            children.removeAll(visited);
            toVisit.addAll(children);
          }
        }
      }
    }

    return visited;
  }

  private static Set<String> getUsedIdentifiers(String formatString) {
    Tokenizer tokenizer = new Tokenizer();
    List<Token<IMatchable>> tokens = tokenizer.tokenize(formatString, new IMatchString() {
      public IMatchable getMatchable(String param) {
        return new FakeIMatchable(param);
      }
    });

    Set<String> usedIdentifiers = new HashSet<String>();

    for (Token<IMatchable> token : tokens) {
      if (token.match != null) {
        usedIdentifiers.add(token.match.getIdentifier());
      }
    }
    return usedIdentifiers;
  }

  private static class FakeIMatchable implements IMatchable {

    private final String id;

    public FakeIMatchable(String id) {
      this.id = id;
    }

    @Override
    public String getIdentifier() {
      return id;
    }

    @Override
    public Option<?> getMatchingOption(String argumentString, int index) {
      return null;
    }

    @Override
    public boolean hasAtLeastOneOptionWithValue() {
      return false;
    }

  }
  
  public DSLParseResult checkProperties() {
    DSLParseResult result = new DSLParseResult();
    
    for (OptionDescription option : dslInfo.getOptionDescriptions()) {
      try {
        String typeClass = option.getType().getOptionTypeClass();
        Class<?> opClass = Class.forName(typeClass);
        
        Constructor<?>[] constructors = opClass.getConstructors();
        if (constructors.length > 0) {
          Constructor<?> constructor = constructors[0];
          Class<?>[] params = constructor.getParameterTypes();
          if (params.length == 2 && params[0] == String.class && params[1] == String.class) {
            Object[] args = { option.getIdentifier(), OptionType.unifyRegexps(option.getPrefixRegexps()) };
            Object instance = constructor.newInstance(args);
            if (instance instanceof Option<?>) {
              Option<?> optionInstance = (Option<?>)instance;
              boolean hasChoices = false;
              for (Pair<String,String> property : option.getProperties()) {
                try {
                  optionInstance.setProperty(property.getFirst(), property.getSecond());
                } catch (InvalidOptionPropertyValueException e) {
                  result.addError(new PropertyValueError(dslInfo.getPropertyValueLocation(property), property.getFirst(), option.getIdentifier(), e.getMessage()));
                }
                hasChoices |= "choices".equals(property.getFirst());
              }
              if (optionInstance instanceof IEnumOption && !hasChoices) {
                result.addError(new MissingPropertyError(option.getSourceLocation(), option.getIdentifier(), "choices"));
              }
            }
          }
        }
      } catch (ClassNotFoundException cnfe) {
        //TODO not on classpath error
      } catch (IllegalArgumentException e) {
      } catch (InstantiationException e) {
      } catch (IllegalAccessException e) {
      } catch (InvocationTargetException e) {
      }
    }
    
    return result;
  }

}
