import java.util.*;

/**
 * An abstract class corresponding to the interface {@code IDefault}.
 *
 * @author Mikolas Janota
 */
public abstract class OptionDefaults implements IDefault  {
    private final String explanation;
    
    public OptionDefaults(String explanation) {
        this.explanation = explanation;
    }
}
