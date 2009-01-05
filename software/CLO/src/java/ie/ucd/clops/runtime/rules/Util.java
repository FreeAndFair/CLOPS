package ie.ucd.clops.runtime.rules;

import ie.ucd.clops.runtime.options.Option;
import ie.ucd.clops.runtime.options.OptionStore;

public class Util {

  public static int countSetOptions(String[] optionIds, OptionStore optionStore) {
    int count = 0;
    for (String optionId : optionIds) {
      Option<?> option = optionStore.getOptionByIdentifier(optionId);
      if (option != null) {
        if (option.hasValue()) {
          count++;
        }
      }
    }
    return count;
  }
  
}
