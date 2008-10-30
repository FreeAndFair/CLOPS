package ie.ucd.clops.dsl.structs;

/**
 *
 * @author Fintan
 *
 */
public interface OptionType {

  static final int BOOLEAN_TYPE = 0;
  static final int STRING_TYPE = 1;
  static final int INTEGER_TYPE = 2;
  static final int FLOAT_TYPE = 3;
  
  int getType();
  
  static final OptionType BOOLEAN = new BasicOptionType(BOOLEAN_TYPE);
  static final OptionType STRING = new BasicOptionType(STRING_TYPE);
  static final OptionType INTEGER = new BasicOptionType(INTEGER_TYPE);
  static final OptionType FLOAT = new BasicOptionType(FLOAT_TYPE);
  
}

class BasicOptionType implements OptionType {
  private int type;
  public BasicOptionType(final int type) {
    this.type = type;
  }
  public int getType() {
    return type;
  }
}