package ie.ucd.clops.documentation;

/**
 * <BON>
 * class_chart OPTION_DESCRIPTION
 * indexing
 *   in_cluster: "DOCUMENTATION"
 * explanation 
 *   "Informal textual description of the purpose, format, dependencies and behaviour of a command line option"
 * query
 *   "What is the name of the option?",
 *   "What is the short description?",
 *   "What is the long explanation?"
 * end
 * </BON>
 * <JML>
 *   refines "OptionDescription.spec"
 * </JML>
 */

 public class OptionDescription {
	private String name;
	private String description;
	private String explanation;
	public String getName() {
		return name;
	}
	public String getDescription() {
		return description;
	}
	public String getExplanation() {
		return explanation;
	}
	

}
