package ie.ucd.clops.codegeneration;

public class GeneratedStatement {

  private final String content;
  private final boolean needsSemi;

  public GeneratedStatement(String content) {
    this.content = content;
    this.needsSemi = true;
  }

  public GeneratedStatement(String content, boolean needsSemi) {
    this.content = content;
    this.needsSemi = needsSemi;
  }

  public String getContent() {
    return content;
  }

  public boolean needsSemi() {
    return needsSemi;
  }

}
