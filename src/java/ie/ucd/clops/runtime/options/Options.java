package ie.ucd.clops.runtime.options;


/**
 * Provides convenience functions for implementing an {@code Option}.
 */
public class Options {
  private Options() { /* prevent instantiation and subclassing */ }

  public static boolean parseBooleanProperty(String name, String val)
  throws InvalidOptionPropertyValueException {
    if (!val.equalsIgnoreCase("true") && !val.equalsIgnoreCase("false")) {
      throw new InvalidOptionPropertyValueException(
        "The value of " + name + " must be true or false, not " + val + ".");
    }
    return Boolean.parseBoolean(val);
  }
}
