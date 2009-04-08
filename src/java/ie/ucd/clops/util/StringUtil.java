package ie.ucd.clops.util;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
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
    System.out.println("Before: " + aliases);
    final StringBuilder sb = new StringBuilder();
    for (String alias : aliases) {
      sb.append(alias.replace("-", "\\-").replace("\\\\?", "?"));
      sb.append(", ");
    }
    if (sb.length() > 1) {
      sb.delete(sb.length() - 2, sb.length());
    }

    System.out.println("After: " + sb.toString());
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

  public static Map<String, String> parseChoice(String choice) {
    final Map<String, String> res = new HashMap<String,String>();
    int curr = 0;
    final int len = choice.length();
    while (curr < len) {
      final int start = curr; 
      int comma = choice.indexOf(',', curr);
      int end = comma;
      int strAlias = choice.indexOf('{', curr);
      int endAlias = comma;
      if (end == -1) {
        end = len;
      }
      if (strAlias != -1 && strAlias < comma) {
        end = strAlias - 1;
        strAlias++;
        endAlias = choice.indexOf('}', curr);
        if (endAlias == -1) {
          return null;
        }
        
        comma = choice.indexOf(',', curr);
      }
      else {
        strAlias = start;
        endAlias = end;
      }
      res.put(choice.substring(start, end), choice.substring(strAlias, endAlias));
      curr = endAlias + 1;
    }
    return res;
  }
}
