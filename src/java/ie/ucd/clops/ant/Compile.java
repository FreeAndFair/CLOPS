package ie.ucd.clops.ant;

import org.apache.tools.ant.BuildException;
import org.apache.tools.ant.Task;

import ie.ucd.clops.dsl.Main;
import ie.ucd.clops.dsl.generatedinterface.CLODSLAntTaskBase;
import ie.ucd.clops.dsl.generatedinterface.CLODSLOptionsInterface;

public class Compile extends CLODSLAntTaskBase {
  public Compile() throws Exception {
  }

  @Override public void run(CLODSLOptionsInterface options) 
  throws BuildException {
    try {
      Main m = new Main();
      m.execute(options); // TODO(rgrig): throw BE is false is returned?
    } catch (Exception e) {
      throw new BuildException("Can't run CLOPS ant task: " + e);
    }
  }
}
