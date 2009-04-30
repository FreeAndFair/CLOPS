package ie.ucd.clops.util;

import ie.ucd.clops.runtime.options.OneArgumentOption;
import ie.ucd.clops.runtime.options.Option;
import ie.ucd.clops.runtime.options.OptionStore;

import java.io.PrintStream;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.Comparator;
import java.util.List;

public class OptionUtil {

  public enum SortingOption { ALPHABETICAL_BY_IDENTIFIER, ALPHABETICAL_BY_FIRST_ALIAS, ADDED_ORDER };
  
  public static List<Option<?>> sortOptions(OptionStore store, SortingOption so) {
    
    List<Option<?>> options = store.getOptionsWithoutErrorOption();
    
    if (so == SortingOption.ADDED_ORDER) {
      return options;
    }
    
    List<Option<?>> optionsClone = new ArrayList<Option<?>>(options);
    Collections.sort(optionsClone, getComparator(so));
    return optionsClone;
  }
  
  /**
   * Internal method for creating a comparator for Option objects, according to the
   * supplied SortingOption
   * @param so
   * @return
   */
  private static Comparator<Option<?>> getComparator(final SortingOption so) {
    Comparator<Option<?>> c = null;
    switch (so) {
    case ALPHABETICAL_BY_IDENTIFIER:
      c = new Comparator<Option<?>>() {
        public int compare(Option<?> o1, Option<?> o2) {
          return o1.getIdentifier().compareTo(o2.getIdentifier());
        }
      };
      break;
    case ALPHABETICAL_BY_FIRST_ALIAS:
      c = new Comparator<Option<?>>() {
        public int compare(Option<?> o1, Option<?> o2) {
          String[] o1aliases = o1.getAliases();
          String[] o2aliases = o2.getAliases();
          return o1aliases.length==0 ? -1 : (o2aliases.length==0 ? 1 : o1aliases[0].compareTo(o2aliases[0])); 
        }
      };
    }
    return c;
  }
  
  public static void printOptionsInManFormat(final PrintStream ps, Collection<Option<?>> options) {
    for (Option<?> o : options) {
        ps.println(".TP");
        ps.print(".B \\");
        ps.println(getOptionNamesString(o, ", ", true));
        ps.println(o.getDescription());
    }
  }
  
  private static String getOptionNamesString(Option<?> o, String separator, boolean includeDefaultArgs) {
    StringBuilder sb = new StringBuilder(StringUtil.collectionToString(Arrays.asList(o.getAliases()), ", "));
    
    if (includeDefaultArgs && o instanceof OneArgumentOption) {
      String argName = ((OneArgumentOption<?>)o).getArgumentName();
      if (o.getAliases().length > 0) {
        sb.append('=');  
      }      
      if (argName == null) {
        sb.append("ARG");
      } else {
        sb.append(argName);
      }
    }
    
    return sb.toString();
  }
  
  public static void printOptions(final PrintStream ps, final Collection<Option<?>> options, final int width, final int initialIndent) {
    //Find the longest option names string
    int longestString = 0;
    for (Option<?> o : options) {
      String s = getOptionNamesString(o, ", ", true);
      if (s.length() > longestString) {
        longestString = s.length();
      }
    }
    
    //This is the length all descriptions should be indented
    int indentLength = longestString + initialIndent + 1;
    
    for (Option<?> o : options) {
      for (int i=0; i < initialIndent; i++) {
        ps.print(' ');
      }
      
      String names = getOptionNamesString(o, ", ", true);
      ps.print(names);
      
      int numberOfSpaces = indentLength - names.length() - initialIndent;
      for (int i=0; i < numberOfSpaces; i++) {
        ps.print(' ');
      }
      
      String description = o.getDescription();
      if (description != null) {
        List<String> splitDescription = StringUtil.splitToLength(description, width-2-indentLength);      
        ps.println(splitDescription.get(0));

        for (int i=1; i < splitDescription.size(); i++) {
          for (int j=0; j < indentLength; j++) {
            ps.print(' ');
          }
          ps.println(splitDescription.get(i));
        }
      }
    }
    ps.flush();
  }
  
  public static void printBashCompletionOptionsScript(final PrintStream ps, Collection<Option<?>> options, final String programName) {
    ps.print("#");
    ps.print(programName);
    ps.println(" bash completion.");
    ps.println("#Automatically generated.");
    ps.print("have ");
    ps.print(programName);
    ps.println(" &&");
    ps.print('_');
    ps.print(programName);
    ps.println("()");
    ps.println("{");
    
    ps.println("  local cur prev options prevmatch prevprev prevprevmatch");
    
    ps.println("  #Setup cur and prev");
    ps.println("  cur=${COMP_WORDS[COMP_CWORD]}");
    ps.println("  prev=${COMP_WORDS[COMP_CWORD-1]}");
    
    ps.println("  #Standard options");
    ps.print("  options=' ");
    for (Option<?> o : options) {
        ps.print(getOptionNamesString(o, " ", false));
        ps.print(' ');
    }
    ps.println("'");
    
    ps.println("  #Options taking an arg");
    ps.print("  argoptions=' ");
    for (Option<?> o : options) {
      if (o instanceof OneArgumentOption) {
        ps.print(getOptionNamesString(o, " ", false));
        ps.print(' ');
      }
    }
    ps.println("'");
    ps.println();
    
    ps.println("  #If we're at the first arg");
    ps.println("  if [[ $COMP_CWORD -eq 1 ]]; then");
    ps.println("    COMPREPLY=($( compgen -W \"$options\" -- $cur))");
    ps.println("    _filedir");
    ps.println("    return 0");
    ps.println("  fi");
    ps.println();
    
    ps.println("  #Check if we're past the args section");
    ps.println("  if [[ \"$prev\" != \"\" ]]; then");
    ps.println("    prevmatch=`echo \"$options\" | grep \"\\ $prev\\ \"`");
    ps.println("  fi");
    ps.println("  if [[ \"$prevmatch\" == \"\" ]]; then");
    ps.println("    prevprev=${COMP_WORDS[COMP_CWORD-2]}");
    ps.println("    if [[ \"$prevprev\" != \"\" ]]; then");
    ps.println("      prevprevmatch=`echo \"$argoptions\" | grep \"\\ $prevprev\\ \"`");
    ps.println("    fi");
    ps.println("    if [[ \"$prevprevmatch\" == \"\" ]]; then");
    ps.println("      _filedir");
    ps.println("      return 0");
    ps.println("    fi");
    ps.println("  fi");
    ps.println();
    
    ps.println("  #Standard set of args");
    ps.println("  COMPREPLY=($( compgen -W \"$options\" -- $cur ))");
    ps.println("  _filedir");
    ps.println("  return 0");    
    
    ps.println("} &&");
    ps.print("complete -o filenames -F _");
    ps.print(programName);
    ps.print(' ');
    ps.println(programName);
    ps.println();
    ps.flush();
  }
  
}
