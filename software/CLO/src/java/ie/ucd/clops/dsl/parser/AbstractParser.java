package ie.ucd.clops.dsl.parser;

import ie.ucd.clops.dsl.DefaultOptionTypeFactory;
import ie.ucd.clops.dsl.OptionTypeFactory;

import org.antlr.runtime.BitSet;
import org.antlr.runtime.IntStream;
import org.antlr.runtime.MismatchedTokenException;
import org.antlr.runtime.Parser;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.TokenStream;

/**
 * Superclass to the antlr generated parser for DSLs.
 * Modifies some of the recovery/error-reporting behaviour,
 * as well as storing some specific information to parsing DSLS.
 * 
 * @author Fintan
 */
public abstract class AbstractParser extends Parser {

  private boolean validParse;
  private OptionTypeFactory optionTypeFactory;
  private String customErrorMessage;
  
  private DSLInformation dslInformation;
  
  public AbstractParser(TokenStream ts) {
    super(ts);
    validParse = true;
    optionTypeFactory = new DefaultOptionTypeFactory();
    dslInformation = new DSLInformation();
  }

  public void displayRecognitionError(String[] tokenNames, RecognitionException e) {
    super.displayRecognitionError(tokenNames, e);
    this.validParse = false;
  }
  
  
  
  /* (non-Javadoc)
   * @see org.antlr.runtime.BaseRecognizer#mismatch(org.antlr.runtime.IntStream, int, org.antlr.runtime.BitSet)
   */
  @Override
  protected void mismatch(IntStream input, int ttype, BitSet follow)
      throws RecognitionException {
    if (customErrorMessage != null) {
      throw new MismatchedTokenException(ttype, input);
    }
    super.mismatch(input, ttype, follow);
  }

  /* (non-Javadoc)
   * @see org.antlr.runtime.BaseRecognizer#recoverFromMismatchedSet(org.antlr.runtime.IntStream, org.antlr.runtime.RecognitionException, org.antlr.runtime.BitSet)
   */
  @Override
  public void recoverFromMismatchedSet(IntStream input, RecognitionException e,
      BitSet follow) throws RecognitionException {
    if (customErrorMessage != null) {
      throw e;
    }
    super.recoverFromMismatchedSet(input, e, follow);
  }

  /* (non-Javadoc)
   * @see org.antlr.runtime.BaseRecognizer#recoverFromMismatchedToken(org.antlr.runtime.IntStream, org.antlr.runtime.RecognitionException, int, org.antlr.runtime.BitSet)
   */
  @Override
  public void recoverFromMismatchedToken(IntStream input,
      RecognitionException e, int ttype, BitSet follow)
      throws RecognitionException {
    if (customErrorMessage != null) {
      throw e;
    }
    super.recoverFromMismatchedToken(input, e, ttype, follow);
  }
  
  public boolean isValidParse() {
    return validParse;
  }

  /**
   * @return the optionTypeFactory
   */
  public OptionTypeFactory getOptionTypeFactory() {
    return optionTypeFactory;
  }

  /**
   * @return the customErrorMessage
   */
  public String getCustomErrorMessage() {
    return customErrorMessage;
  }

  /**
   * @param customErrorMessage the custom error message to set
   */
  public void setCustomErrorMessage(String customErrorMessage) {
    this.customErrorMessage = customErrorMessage;
  }

  public DSLInformation getDslInformation() {
    return dslInformation;
  }

  protected static String stripStringMarks(String s) {
    return s.substring(1,s.length()-1);
  }
  
}
