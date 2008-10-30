package ie.ucd.clops.runtime.options;

import ie.ucd.clops.runtime.parser.ProcessingResult;

import java.util.Set;

/**
 * @author Viliam Holub
 * @author Mikolas Janota
 * @author Fintan
 */
public class IntegerOption extends BasicOption {
	private Integer value;

	public IntegerOption(String identifier, final Set<String> aliases) {
		super(identifier, aliases);
	}

	public IntegerOption(String identifier) {
		super(identifier);
	}

	/* (non-Javadoc)
	 * @see ie.ucd.clo.runtime.options.Option#getType()
	 */
	public OptionType getType() { return OptionType.INTEGER; }

	/* (non-Javadoc)
	 * @see ie.ucd.clo.runtime.options.Option#getValue()
	 */
	public Object getValue() { return value; }

	/* (non-Javadoc)
	 * @see ie.ucd.clo.runtime.options.Option#hasValue()
	 */
	public boolean hasValue() {
		return value != null;
	}

	/* (non-Javadoc)
	 * @see ie.ucd.clo.runtime.options.Option#match(java.lang.String[], int)
	 */
	public ProcessingResult process(String[] args, int offset) {
		String currentArg = args[offset];
		assert this.getMatchingOption(currentArg) == this;
		String alias = getMatchingAlias(currentArg);
		try {
			//If we allow -arg=VALUE
			if (currentArg.length() > alias.length() && currentArg.charAt(alias.length()) == '=') {
				// -arg=VALUE format
				setFromString(currentArg.substring(alias.length() + 1));
				return ProcessingResult.successfulProcess(1);
			} else {
				// Next parameter
				if (offset >= args.length)
					return ProcessingResult.erroneousProcess( "Parameter expected");
				setFromString( args[offset+1]);
				return ProcessingResult.successfulProcess(2);
			}
		}
		catch (InvalidOptionValueException iove) {
			return ProcessingResult.erroneousProcess(iove.getMessage());
		}
	}

	/* (non-Javadoc)
	 * @see ie.ucd.clo.runtime.options.Option#set(java.lang.Object)
	 */
	public void set(Object value) throws InvalidOptionValueException {
		if (value instanceof Integer) {
			this.value = (Integer)value;
		} else {
			throw new InvalidOptionValueException(value + " is not an Integer.");
		}
	}

	public void setFromString(String valueString) throws InvalidOptionValueException {
		if (valueString == null)
			throw new InvalidOptionValueException("Empty integer value.");
		try {
			value = new Integer( valueString);
		}
		catch (NumberFormatException e) {
			throw new InvalidOptionValueException(valueString + " is not an integer number.");
		}		
	}

	/* (non-Javadoc)
	 * @see ie.ucd.clo.runtime.options.Option#unset()
	 */
	public void unset() {
		this.value = null;
	}
}
