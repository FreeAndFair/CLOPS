package ie.ucd.clops.util;

import java.util.LinkedList;
import java.util.List;
import java.util.StringTokenizer;

public class StringUtil {

  public static List<String> splitToLength(String s, int length) {
    List<String> parts = new LinkedList<String>(); //The list of parts
    StringTokenizer st = new StringTokenizer(s); //Split the string to words
    StringBuilder sb = new StringBuilder();

    while(st.hasMoreTokens()) {
      String next = st.nextToken(); //Next word
      if(sb.length() + next.length() > length) {

        //Handle next.length() > length
        if (sb.length() == 0) {
          //Just add it anyway
          parts.add(next);
          //No need to reset builder
        } else {
          //Remove trailing space
          sb.deleteCharAt(sb.length()-1);
          parts.add(sb.toString());
          sb = new StringBuilder();
        }

      }
      sb.append(next);
      sb.append(' ');
    }

    //Add last part
    if (sb.length() > 0) {
      sb.deleteCharAt(sb.length()-1);
      parts.add(sb.toString());
    }

    return parts;
  }
  
  public static String convertAliasesForManpage(List<String> aliases) {
    System.out.println("Before: " + aliases);
    StringBuilder sb = new StringBuilder();
    for (String alias : aliases) {
      sb.append(alias.replace("-", "\\-").replace("\\\\?", "?"));
      sb.append(", ");
    }
    if (sb.length() > 1) {
      sb.delete(sb.length()-2, sb.length());
    }
    
    System.out.println("After: " + sb.toString());
    return sb.toString();
  }
  
}
