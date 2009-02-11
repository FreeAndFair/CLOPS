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
  
}
