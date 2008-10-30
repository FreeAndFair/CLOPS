package ie.ucd.clops.runtime.parser;

/**
 * 
 * @author Fintan
 *
 */
public class ProcessingResult {

  private final int numberOfArgsConsumed;
  private final boolean errorDuringProcessing;
  private final String errorMessage;
      
  /**
   * 
   * @param numberOfArgsConsumed
   * @param errorDuringProcessing
   * @param errorMessage
   */
  public ProcessingResult(int numberOfArgsConsumed,
      boolean errorDuringProcessing, String errorMessage) {
    super();
    this.numberOfArgsConsumed = numberOfArgsConsumed;
    this.errorDuringProcessing = errorDuringProcessing;
    this.errorMessage = errorMessage;
  }
  
  public static ProcessingResult successfulProcess(final int argsConsumed) {
    return new ProcessingResult(argsConsumed, false, null);
  }
  
  public static ProcessingResult erroneousProcess(final String errorMessage) {
    return new ProcessingResult(0, true, errorMessage);
  }  

  public boolean errorDuringProcessing() {
    return errorDuringProcessing;
  }

  public int getNumberOfArgsConsumed() {
    return numberOfArgsConsumed;
  }

  public String getErrorMessage() {
    return errorMessage;
  }  
  
}
