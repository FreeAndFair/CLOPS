package ie.ucd.clo.dsl;

import org.antlr.runtime.RecognitionException;

/**
 * 
 * @author fintan
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
