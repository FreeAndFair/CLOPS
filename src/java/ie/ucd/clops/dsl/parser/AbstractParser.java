package ie.ucd.clops.dsl.parser;

import ie.ucd.clops.dsl.DefaultOptionTypeFactory;
import ie.ucd.clops.dsl.OptionTypeFactory;
import ie.ucd.clops.dsl.structs.DSLInformation;

import java.io.File;

import org.antlr.runtime.BitSet;
import org.antlr.runtime.IntStream;
import org.antlr.runtime.MismatchedTokenException;
import org.antlr.runtime.Parser;
import org.antlr.runtime.RecognitionException;
import org.antlr.runtime.RecognizerSharedState;
import org.antlr.runtime.Token;
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
  private File sourceFile;
  
  private DSLInformation dslInformation;
  
  public AbstractParser(TokenStream ts, RecognizerSharedState state) {
    super(ts, state);
    validParse = true;
    optionTypeFactory = new DefaultOptionTypeFactory();
    dslInformation = new DSLInformation();
  }

  public void setSourceFile(File file) {
    this.sourceFile = file;
  }

  public void displayRecognitionError(String[] tokenNames, RecognitionException e) {
    super.displayRecognitionError(tokenNames, e);
    this.validParse = false;
  }  
  
  /* (non-Javadoc)
   * @see org.antlr.runtime.BaseRecognizer#mismatch(org.antlr.runtime.IntStream, int, org.antlr.runtime.BitSet)
   */
//  @Override
//  protected void mismatch(IntStream input, int ttype, BitSet follow)
//      throws RecognitionException {
//    if (customErrorMessage != null) {
//      throw new MismatchedTokenException(ttype, input);
//    }
//    super.mismatch(input, ttype, follow);
//  }

  /*
   * @see org.antlr.runtime.BaseRecognizer#recoverFromMismatchedToken(org.antlr.runtime.IntStream, org.antlr.runtime.RecognitionException, int, org.antlr.runtime.BitSet)
   */
  @Override
  public Object recoverFromMismatchedToken(IntStream input, int ttype, BitSet follow)
      throws RecognitionException {
    if (customErrorMessage != null) {
      throw new MismatchedTokenException(ttype, input);
    }
    return super.recoverFromMismatchedToken(input, ttype, follow);
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
  
  public final SourceLocation getSourceLocation(Token t) {
    return new SourceLocation(t, this.sourceFile);
  }
  
  public final SourceLocation getSourceLocation(Token tStart, Token tEnd) {
    return new SourceLocation(tStart, tEnd, this.sourceFile);
  }
  
  //Just a shorter version
  public final SourceLocation getSLoc(Token t) {
    return getSourceLocation(t);
  }
  
  //Just a shorter version
  public final SourceLocation getSLoc(Token tStart, Token tEnd) {
    return getSourceLocation(tStart, tEnd);
  }
  
  public final SourceLocation getSLoc(SourceLocation start, SourceLocation end) {
  return new SourceLocation(start, end);
  }
}
