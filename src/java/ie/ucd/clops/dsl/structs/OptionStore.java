package ie.ucd.clops.dsl.structs;

import java.util.HashMap;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;

public class OptionStore {
  /** true if the object is sealed (immutable). */ 
  private boolean isPacked;
  private final List<OptionDescription> optionDescriptions;
  
  private final Map<String, OptionDescription> optionNameMap; // Name -> OpDesc
  private final Map<String, OptionGroupDescription> optionGroupNameMap; // Name -> OpGroupDesc
  /** keep track of all options and groups. */
  private final Map<String, OptionDescription> optionAndGroupNameMap;
  
  
  private final List<OptionGroupDescription> optionGroupDescriptions;

  public OptionStore() {
    optionDescriptions = new LinkedList<OptionDescription>();
    optionAndGroupNameMap = new HashMap<String, OptionDescription>();
    optionNameMap = new HashMap<String, OptionDescription>();
    optionGroupNameMap = new HashMap<String, OptionGroupDescription>();
    optionGroupDescriptions = new LinkedList<OptionGroupDescription>();
  }

  
  
  public void addOptionDescription(OptionDescription optionDescription) {
    assert (!isPacked);
    optionDescriptions.add(optionDescription);
    optionAndGroupNameMap.put(optionDescription.getIdentifier(), optionDescription);
    optionNameMap.put(optionDescription.getIdentifier(), optionDescription);
  }
  
  public List<OptionDescription> getOptionDescriptions() {
    return optionDescriptions;
  }
  
  public void addOptionGroupDescription(OptionGroupDescription group) {
    assert (!isPacked);
    optionGroupDescriptions.add(group);
    optionAndGroupNameMap.put(group.getIdentifier(), group);
    optionGroupNameMap.put(group.getIdentifier(), group);
  }
  
  public List<OptionGroupDescription> getOptionGroupDescriptions() {
    return optionGroupDescriptions;
  }
  
  
  public OptionDescription getOptionDescriptionForIdentifier(String id) {
    final OptionDescription od =  optionAndGroupNameMap.get(id);
    return od;
  }
  
  public String getOptionValuTypeParameterisationForIdentifier(String identifier) {
    final OptionDescription od = getOptionDescriptionForIdentifier(identifier);
    return od == null ? null : od.getType().getOptionValueTypeParameterisation();
  }

  /** 
   * Packs the object: make sure that every value has
   * been properly set and makes it immutable.
   */
  public void pack() {
    isPacked = true;
    //TODO Create and add AllOptionsGroup
    //TODO Only expand and include groups that are in format string?
    for (OptionGroupDescription og : optionGroupDescriptions) {
      og.expand(optionNameMap, optionGroupNameMap);
    }
  }
}
