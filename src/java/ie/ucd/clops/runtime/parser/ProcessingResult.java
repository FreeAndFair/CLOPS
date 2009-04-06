package ie.ucd.clops.runtime.parser;

/**
 * 
 * @author Fintan
 *
 */
public class ProcessingResult {

  private final boolean errorDuringProcessing;
  private final String errorMessage;
      
  /**
   * @param errorDuringProcessing
   * @param errorMessage
   */
  public ProcessingResult(boolean errorDuringProcessing, String errorMessage) {
    super();
    this.errorDuringProcessing = errorDuringProcessing;
    this.errorMessage = errorMessage;
  }
  
  public static ProcessingResult successfulProcess() {
    return new ProcessingResult(false, null);
  }
  
  public static ProcessingResult erroneousProcess(final String errorMessage) {
    return new ProcessingResult(true, errorMessage);
  }  

  public boolean errorDuringProcessing() {
    return errorDuringProcessing;
  }

  public String getErrorMessage() {
    return errorMessage;
  }  
  
}
