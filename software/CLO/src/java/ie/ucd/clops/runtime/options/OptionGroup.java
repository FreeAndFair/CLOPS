package ie.ucd.clops.runtime.options;

import java.util.ArrayList;
import java.util.Collection;
import java.util.Set;
import java.util.HashSet;

/**
 * 
 * @author Fintan
 * @author Viliam Hollub
 * @author Mikolas Janota
 * 
 * A group of Options. Each OptionGroup is structurally a collection of Options
 * and OptionGroups.
 *
 */
public class OptionGroup extends MatchableCollection implements IMatchable {
    private String identifier;

    //TODO: ensure uniqnuess in a nicer way
    private static Set<String> groupIds = new HashSet<String>();// debugging

    /**
     * Create an {@code OptionGroup} with the provided identifier.
     * @param identifier a unique identifier for this {@code OptionGroup}.
     */
    public OptionGroup(String identifier) {
        assert !groupIds.contains(identifier);
        groupIds.add(identifier); // debugging
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
