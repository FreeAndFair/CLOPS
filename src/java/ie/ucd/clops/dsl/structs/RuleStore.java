package ie.ucd.clops.dsl.structs;

import java.util.LinkedList;
import java.util.List;

public class RuleStore extends OptionStore {
  
  /** true if the object is sealed (immutable). */ 
  private boolean isPacked;

  
  private boolean transitiveFlyrules;
  
  
  private final List<FlyRuleDescription> flyRuleDescriptions;
  private final List<OverrideRuleDescription> overrideRuleDescriptions;
  private final List<ValidityRuleDescription> validityRuleDescriptions;

  public RuleStore () {
    flyRuleDescriptions = new LinkedList<FlyRuleDescription>();
    overrideRuleDescriptions = new LinkedList<OverrideRuleDescription>();
    validityRuleDescriptions = new LinkedList<ValidityRuleDescription>();
  }
  public boolean getTransitiveFlyrules() { 
    return transitiveFlyrules; 
  }
  
  public void setTransitiveFlyRules(boolean b) {
    assert (!isPacked);
    transitiveFlyrules = b;
  }
  

  public void addFlyRuleDescription(FlyRuleDescription flyRuleDescription) {
    assert (!isPacked);
    flyRuleDescriptions.add(flyRuleDescription);
  }
  
  public void addOverrideRuleDescription(OverrideRuleDescription overrideRuleDescription) {
    assert (!isPacked);
    overrideRuleDescriptions.add(overrideRuleDescription);
  }
    
  public void addValidityRuleDescription(ValidityRuleDescription validityRuleDescription) {
    assert (!isPacked);
    validityRuleDescriptions.add(validityRuleDescription);
  }
  
  public List<FlyRuleDescription> getFlyRuleDescriptions() {
    return flyRuleDescriptions;
  }
  public List<OverrideRuleDescription> getOverrideRuleDescriptions() {
    return overrideRuleDescriptions;
  }

  public List<ValidityRuleDescription> getValidityRuleDescriptions() {
    return validityRuleDescriptions;
  }
  
  /** {@inheritDoc} */
  @Override
  public void pack() {
    super.pack();
    processPlaceholders();
    isPacked = true;
  }
  
  private void processPlaceholders() {
    for (RuleDescription rule : getFlyRuleDescriptions()) {
      rule.processPlaceHolders(this);
    }
    for (RuleDescription rule : getOverrideRuleDescriptions()) {
      rule.processPlaceHolders(this);
    }
    for (ValidityRuleDescription rule : getValidityRuleDescriptions()) {
      rule.processPlaceHolders(this);
    }
  }
}
