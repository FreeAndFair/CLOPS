import java.util.HashMap;
import java.util.HashSet;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

/**
 * Provide a basic abstract superclass for OptionDefs that allows for clean
 * and simple subclasses.
 * @author fintan
 *
 */
public class AbstractOptionDefs implements IOptionDefs {

	private final Map<String, Option> optionsMap;
	private final Set<Option> options;
	private final List<OptionOverride> overrides;
	private final String objectDefsName;
	private final List<IDefault> defaults;
	private final List<IConstraint> constraints;
	
	public AbstractOptionDefs(String objectDefsName) {
		this.objectDefsName = objectDefsName;
		this.optionsMap = new HashMap<String, Option>();
		this.options = new HashSet<Option>();
		this.overrides = new LinkedList<OptionOverride>();
		this.defaults = new LinkedList<IDefault>();
		this.constraints = new LinkedList<IConstraint>();
	}
	
	public void addOption(String... optionNames) {
		assert optionNames.length > 0;
		Option option = Option.registerOption(optionNames);
		options.add(option);
		for (String s : optionNames) {
			optionsMap.put(s, option);
		}
	}
	
	public Option getOption(String optionName) {
		return optionsMap.get(optionName);
	}
	
	public void addOverride(OptionOverride override) {
		overrides.add(override);
	}

	public Boolean getOverride(OptVals vals, Option opt) {
	  Boolean retv = null;
    for (OptionOverride override : overrides) {
      Boolean overrideVal = getOverride(vals, opt);
      if (override != null) {
        assert retv == null || retv.equals(overrideVal);
        retv = overrideVal;
      }
    }
    return retv;
	}
	
	public void addDefault(IDefault def) {
	  defaults.add(def);
	}

	public Boolean getDefault(OptVals vals, Option opt) {
		for (IDefault def : defaults) {
		  Boolean retVal = def.getDefault(vals, opt);
		  if (retVal != null) {
		    return retVal;
		  }
		}
		return null;
	}
	
	public void addConstraint(IConstraint constraint) {
	  constraints.add(constraint);
	}

	public boolean isValid(OptVals vals) {
		for (IConstraint constraint : constraints) {
		  if (!constraint.isValid(vals)) {
		    return false;
		  }
		}
		return true;
	}
	
	

}
