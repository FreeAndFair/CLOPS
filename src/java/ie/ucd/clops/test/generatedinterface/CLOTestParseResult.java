package ie.ucd.clops.test.generatedinterface;

import ie.ucd.clops.runtime.errors.ParseResult;

/**
 * A parse result for the CLOTestParser.
 * @author The CLOPS team
 */
public class CLOTestParseResult extends ParseResult {

  private CLOTestOptionStore optionStore;

  public CLOTestParseResult(ParseResult parseResult, CLOTestOptionStore optionStore) {
    super(parseResult);
    this.optionStore = optionStore;
  }

  public CLOTestOptionStore getOptionStore() {
    return optionStore;
  }

} 