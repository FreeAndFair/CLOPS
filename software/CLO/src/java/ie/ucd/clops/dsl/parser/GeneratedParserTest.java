package ie.ucd.clops.dsl.parser;

import java.lang.reflect.Constructor;
import java.lang.reflect.InvocationTargetException;
import java.lang.reflect.Method;


public class GeneratedParserTest {

  /**
   * @param args
   */
  public static void main(String[] args) {
    
    if (args.length < 1) {
      System.out.println("Error");
    } else {
      
      try {
        Class c = Class.forName(args[0]);

        String[] newArgs = new String[args.length-1];
        System.arraycopy(args, 1, newArgs, 0, args.length-1);
        
        Constructor[] constructors = c.getConstructors();
        assert constructors.length == 1;
        Constructor constructor = constructors[0];

        Object o = constructor.newInstance();

        Method m = c.getMethod("parse", String[].class);
        m.invoke(o, new Object[] { newArgs });
        
      } catch (ClassNotFoundException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      } catch (SecurityException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      } catch (NoSuchMethodException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      } catch (IllegalArgumentException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      } catch (InstantiationException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      } catch (IllegalAccessException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      } catch (InvocationTargetException e) {
        // TODO Auto-generated catch block
        e.printStackTrace();
      }
    }


   
  }

}
