package ie.ucd.clops.runtime.options;

/**
 * 
 * @author Fintan
 * @author Viliam Holub
 * @author Mikolas Janota
 * 
 * A class representing an option group. 
 * Each option group is structurally a collection of {@code Option}s
 * or another option groups.
 *
 */
public class OptionGroup extends MatchableCollection implements IMatchable {
  private String identifier;


  /**
   * Create an {@code OptionGroup} with the provided identifier.
   * @param identifier a unique identifier for this {@code OptionGroup}.
   */
  public OptionGroup(String identifier) {
    this.identifier = identifier;
  }

  /**
   * Add an {@code IMatchable} object to this group.
   * @param option the Option or OptionGroup to add.
   */
  public void addOptionOrGroup( IMatchable option) {
    add(option);
  }


  /*@pure*/public String getIdentifier() {
    return identifier;
  }

  @Override
  public String toString() {
    return "Option Group: \"" + getIdentifier() + "\"";
  }

  @Override
  public boolean equals(Object obj) {
    boolean retv;
    if (obj instanceof OptionGroup) {
      OptionGroup oog = (OptionGroup)obj;
      retv = this.getIdentifier().equals(oog.getIdentifier());
      assert !retv || super.equals(oog); 
    } else {
      retv = false;
    }

    return retv;
  }

  @Override
  /*@pure*/public int hashCode() {
    return getIdentifier().hashCode();
  }

}
