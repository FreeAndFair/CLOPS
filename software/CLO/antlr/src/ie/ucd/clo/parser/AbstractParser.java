package ie.ucd.clo.parser;

import org.antlr.runtime.Parser;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.TokenStream;

/**
 * @author Fintan
 */
public abstract class AbstractParser extends Parser {

  private boolean validParse;
  
  public AbstractParser(TokenStream ts) {
    super(ts);
    validParse = true;
  }

  public void displayRecognitionError(String[] tokenNames, RecognitionException e) {
    super.displayRecognitionError(tokenNames, e);
    this.validParse = false;
  }
  
  public boolean isValidParse() {
    return validParse;
  }
}
