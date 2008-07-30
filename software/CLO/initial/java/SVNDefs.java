

/**
 * Description of the svn options.
 *
 * @author Fintan Fairmichael
 */
public class SVNDefs extends AbstractOptionDefs {


  public SVNDefs() {
    super("svn");
    //TODO: Add all option aliases

    //Subcommands
    addOption("add");
    addOption("add");
    addOption("blame", "praise", "annotate", "ann");
    addOption("cat");
    addOption("checkout");
    addOption("cleanup");
    addOption("commit");
    addOption("copy");
    addOption("delete");
    addOption("diff");
    addOption("export");
    addOption("help");
    addOption("import");
    addOption("info");
    addOption("list");
    addOption("lock");
    addOption("log");
    addOption("merge");
    addOption("mkdir");
    addOption("move");
    addOption("propdel");
    addOption("propedit");
    addOption("propget");
    addOption("proplist");
    addOption("propset");
    addOption("resolved");
    addOption("revert");
    addOption("status");
    addOption("switch");
    addOption("unlock");
    addOption("update");

    //options
    addOption(new String[] {"-v", "--verbose"});
    addOption(new String[] {"-q", "--quiet"});
    addOption(new String[] {"--auto-props"});
    addOption(new String[] {"--no-auto-props"});
    
    //Overrides
    addOverride(new Cancel("verbose cancels quiet", getOption("-v"), getOption("-q")));

    //Constraints
    addConstraint(new MutuallyExclusiveConstraint("Ñ-auto-props", "--no-auto-props"));
  }

}