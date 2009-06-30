package ie.ucd.clops.ant;

import ie.ucd.clops.dsl.Main;
import ie.ucd.clops.dsl.generatedinterface.CLODSLAntTaskBase;
import ie.ucd.clops.dsl.generatedinterface.CLODSLOptionsInterface;

import org.apache.tools.ant.BuildException;

public class Compile extends CLODSLAntTaskBase {
  public Compile() throws Exception {
  }

  public void run(CLODSLOptionsInterface options) 
  throws BuildException {
    try {
      final Main m = new Main();
      m.execute(options); // TODO(rgrig): throw BE is false is returned?
    } catch (Exception e) {
      throw new BuildException("Can't run CLOPS ant task: " + e);
    }
  }
}
