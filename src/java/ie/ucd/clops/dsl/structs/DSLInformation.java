package ie.ucd.clops.dsl.structs;


import ie.ucd.clops.dsl.parser.SourceLocation;

import java.util.Set;

/**
 * Simple AST-like datastructure for storing the information gathered
 * from parsing a DSL file.
 * 
 * Once all the informations are gathered the {@link #pack()} method
 * must be called to seal the object.
 * 
 * @author Fintan
 *
 */
public class DSLInformation extends RuleStoreDescription {
  /** true if the object is sealed (immutable). */ 
  private boolean isPacked;
  /** name of the program which is specified in the name section. */
  private String name = "";
  /** description of the program. */
  private String description = "";
  /** the package name of the generated parser files. */
  private String packageName = "";
  /** the structure containing correspondence between classes long and short names. */
  private NameDict dict;


  
  private String formatString = "";
  private SourceLocation formatSourceLocation;
  private String formatDesc = "";
  
  public DSLInformation() {
    isPacked = false;
  }

  public String getFormatString() {
    return formatString;
  }
  
  public void setFormatString(String formatString) {
    assert (!isPacked);
    this.formatString = formatString;
  }
  
  public void setFormatSourceLocation(SourceLocation formatSourceLocation) {
    this.formatSourceLocation = formatSourceLocation;
  }

  public SourceLocation getFormatSourceLocation() {
    return formatSourceLocation;
  }

  public String getParserName() {
    return name;
  }

  public void setParserName(String parserName) {
    assert (!isPacked);
    this.name = parserName;
  }

  public String getPackageName() {
    return packageName;
  }

  public void setPackageName(String packageName) {
    assert (!isPacked);
    this.packageName = packageName;
  }

  public Set<String> getTypeImports() {
    assert (isPacked);
    return dict.getTypeImports();
  }
  public Set<String> getValueTypeImports() {
    assert (isPacked);
    return dict.getValueTypeImports();
  }
  

  public String getTypeClass(OptionDescription od) {
    assert (isPacked);
    return dict.getTypeClass(od);
  }
  public String getValueTypeClass(OptionDescription od) {
    assert (isPacked);
    return dict.getValueTypeClass(od);
  }
  
  /** {@inheritDoc} */
  @Override
  public void pack() {
    super.pack();
    setFormatString(formatString);
    dict = new NameDict(getOptionDescriptions());
    isPacked = true;
  }

  /**
   * Adds a description to the parser.
   * @param st the description string
   */
  public void setParserDescription(final String st) {
    assert (!isPacked);
    description = st.replace("\n"," ").replace("\r"," ");
  }

  public String getDescription() {
    return description;
  }
  
  /**
   * Adds a description to the parser.
   * @param st the description string
   */
  public void setFormatDescription(final String st) {
    assert (!isPacked);
    formatDesc = st;
  }
  
  public String getFormatDescription() {
    return formatDesc;
  }
  
  
  
}
