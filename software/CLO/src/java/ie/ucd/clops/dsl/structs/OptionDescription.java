package ie.ucd.clops.dsl.structs;

import ie.ucd.clops.dsl.OptionType;

import java.util.List;
import java.util.Map;

/**
 *
 * @author Mikolas
 * @author Fintan
 *
 */
public interface OptionDescription {

  /**
   * Set this option's String identifier.
   * @param id this options's identifier.
   */
  void setId(final String id);
  
  /**
   * Get this option's String identifier as specified in the DSL.
   * @return this option's identifier.
   */
  String getIdentifier();

  /**
   * 
   * @param type
   */
  void setType(final OptionType type);
  
  /**
   * Get the type of this option.
   * @return this option's type.
   */
  OptionType getType();

  /**
   * Get the regular expressions for the prefix of this option.
   * @return the Set of prefixes.
   */
  List<String> getPrefixRegexps();

  /**
   * Add a prefix regular expression for this option.
   * @param regexp the regular expression to add for this option.
   */
  void addPrefixRegexp(final String regexp);
  
  /**
   * Set a property key,value pair for this option.
   * @param key the property key to set.
   * @param value the property value to set.
   */
  void setProperty(final String key, final String value);
  
  /**
   * Get the properties associated with this option.
   * @return the properties associated with this option.
   */
  Map<String,String> getProperties();
}
