package ie.ucd.clops.dsl.parser;

import org.antlr.runtime.RecognitionException;

/**
 * An Exception that occurs during parsing of the DSL.
 * @author Fintan
 *
 */
public class DSLParseException extends RecognitionException {

  private static final long serialVersionUID = -4554218055743899739L;
  
  private String message;
  
  public DSLParseException(String message) {
    this.message = message;
  }

  /* (non-Javadoc)
   * @see java.lang.Throwable#toString()
   */
  @Override
  public String toString() {
    return message;
  }  
  
}
