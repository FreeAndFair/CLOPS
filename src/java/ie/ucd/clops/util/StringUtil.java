package ie.ucd.clops.util;

import java.util.ArrayList;
import java.util.Collection;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Scanner;
import java.util.StringTokenizer;

public class StringUtil {

  public static List<String> splitToLength(String s, int length) {
    final List<String> parts = new LinkedList<String>(); //The list of parts
    final StringTokenizer st = new StringTokenizer(s); //Split the string to words
    StringBuilder sb = new StringBuilder();

    while (st.hasMoreTokens()) {
      final String next = st.nextToken(); //Next word
      if (sb.length() + next.length() > length) {

        //Handle next.length() > length
        if (sb.length() == 0) {
          //Just add it anyway
          parts.add(next);
          //No need to reset builder
        } 
        else {
          //Remove trailing space
          sb.deleteCharAt(sb.length() - 1);
          parts.add(sb.toString());
          sb = new StringBuilder();
        }

      }
      sb.append(next);
      sb.append(' ');
    }

    //Add last part
    if (sb.length() > 0) {
      sb.deleteCharAt(sb.length() - 1);
      parts.add(sb.toString());
    }

    return parts;
  }

  public static String convertAliasesForManpage(List<String> aliases) {
    final StringBuilder sb = new StringBuilder();
    for (String alias : aliases) {
      sb.append(alias.replace("-", "\\-").replace("\\\\?", "?"));
      sb.append(", ");
    }
    if (sb.length() > 1) {
      sb.delete(sb.length() - 2, sb.length());
    }
    return sb.toString();
  }
  

  /**
   * Produces java String constant containing a given String
   * that may contain newlines.
   * @param s
   */
  public static List<String> quoteMultilineString(final String s) {
    final String[] lines = s.split("\n");
    final List<String> result = new LinkedList<String>();

    for (String line : lines) {
      line = line.trim();
      if (line.equals("")) {
        continue;
      }
      result.add(line);
    }
    if (result.size() == 0) {
      result.add("\"\"");
    }
    return result;
  }
  
  /**
   * Make a java list out of comma separated list of string.
   * @param list the list to parse of the form "a,b,c,d"
   * @return a java list ["a", "b", "c", "d"]
   */
  public static List<String> mkList(final String list) {
    final String[] arr = list.split(",");
    final List<String> res = new ArrayList<String>();
    if (arr.length == 0) {
      res.add(list);
    }
    else {
      for (String s:arr) {
        res.add(s.trim());
      }
    }
    return res;
  }

  public static Map<String, StringBuilder> parseChoice(String choice) {
    final Map<String, StringBuilder> map = new HashMap<String, StringBuilder>();
    final String[] parts = choice.split(",");
    for (String part : parts) {
      parseChoicePart(part, map);
    }
    return map;
  }
  
  private static void parseChoicePart(String part, Map<String, StringBuilder> map) {
    String name, parseString;
    final int index = part.indexOf('(');
    if (index != -1) {
      parseString = part.substring(0, index);
      name = part.substring(index + 1, part.length() - 1);
    } else {
      parseString = part;
      name = part;
    }
    StringBuilder sb = map.get(name);
    if (sb == null) {
      sb = new StringBuilder('"' + parseString + '"');
      map.put(name, sb);
    } else {
      sb.append(", \"");
      sb.append(parseString);
      sb.append('"');
    }
  }
  
  public static String collectionToString(Collection<?> collection, String separator) {
    StringBuilder sb = new StringBuilder();
    for (Object o : collection) {
     sb.append(o.toString());
     if (separator != null) {
       sb.append(separator);
     }
    }
    if (sb.length() >= separator.length()) {
      sb.delete(sb.length()-separator.length(), sb.length());
    }    
    return sb.toString();
  }
  
  private static List<String> splitTextToLength(String message, int maxLength) {
    List<String> parts = new LinkedList<String>();    
    Scanner scanner = new Scanner(message);    
    StringBuilder currentPart = new StringBuilder();
    while (scanner.hasNext()) {
      String next = scanner.next();
      if ((currentPart.length() + 1 + next.length()) > maxLength) {
        parts.add(currentPart.toString());
        currentPart = new StringBuilder();
        if (next.length() > maxLength) {
          //Split word, it won't fit
          int index = 0;
          while (index < next.length()) {
            parts.add(next.substring(index,index+maxLength));
          }
        } else {
          currentPart.append(next);
        }
      } else {
        if (currentPart.length() > 0) {
          currentPart.append(' ');
        }
        currentPart.append(next);
      }
    }
    if (currentPart.length() > 0) {
      parts.add(currentPart.toString());
    }
    return parts;
  }
}
