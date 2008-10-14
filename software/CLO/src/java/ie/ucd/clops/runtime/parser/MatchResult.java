package ie.ucd.clops.runtime.parser;

/**
 * 
 * @author fintan
 *
 */
public class MatchResult {

  private static final MatchResult NO_MATCH = new MatchResult(false, 0, false, null);
  
  private final boolean matched;
  private final int numberOfArgsConsumed;
  private final boolean errorDuringProcessing;
  private final String errorMessage;
      
  /**
   * 
   * @param matched
   * @param numberOfArgsConsumed
   * @param errorDuringProcessing
   * @param errorMessage
   */
  public MatchResult(boolean matched, int numberOfArgsConsumed,
      boolean errorDuringProcessing, String errorMessage) {
    super();
    this.matched = matched;
    this.numberOfArgsConsumed = numberOfArgsConsumed;
    this.errorDuringProcessing = errorDuringProcessing;
    this.errorMessage = errorMessage;
  }
  
  public static MatchResult positiveMatch(final int argsConsumed) {
    return new MatchResult(true, argsConsumed, false, null);
  }
  
  public static MatchResult negativeMatch() {
    return NO_MATCH;
  }
  
  public static MatchResult erroneousMatch(final String errorMessage) {
    return new MatchResult(false, 0, true, errorMessage);
  }
  

  public boolean errorDuringProcessing() {
    return errorDuringProcessing;
  }

  public boolean matched() {
    return matched;
  }

  public int getNumberOfArgsConsumed() {
    return numberOfArgsConsumed;
  }

  public String getErrorMessage() {
    return errorMessage;
  }  
  
}
