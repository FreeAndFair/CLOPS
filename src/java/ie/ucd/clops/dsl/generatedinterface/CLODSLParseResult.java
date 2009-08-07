package ie.ucd.clops.dsl.generatedinterface;

import ie.ucd.clops.runtime.errors.ParseResult;

/**
 * A parse result for the CLODSLParser.
 * @author The CLOPS team
 */
public class CLODSLParseResult extends ParseResult {

  private CLODSLOptionStore optionStore;

  public CLODSLParseResult(ParseResult parseResult, CLODSLOptionStore optionStore) {
    super(parseResult);
    this.optionStore = optionStore;
  }

  public CLODSLOptionStore getOptionStore() {
    return optionStore;
  }

} 