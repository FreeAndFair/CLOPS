package ie.ucd.clops.dsl.structs;

import ie.ucd.clops.runtime.options.OptionType;

import java.util.Properties;
import java.util.Set;

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
   * Get the aliases associated with this option.
   * @return the Set of aliases.
   */
  Set<String> getAliases();

  /**
   * Add an alias for this option.
   * @param alias the alias to add for this option.
   */
  void addAlias(final String alias);
  
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
  Properties getProperties();
}
