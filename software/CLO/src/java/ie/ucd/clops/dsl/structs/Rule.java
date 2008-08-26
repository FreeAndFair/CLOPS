package ie.ucd.clops.dsl.structs;

public abstract class Rule {
    /**
     * The guard triggering this rule.
     */
    public abstract BooleanExpression getGuard() ;


    /**
     * The option assigned to on the right hand side of the rule.
     */
    public abstract /*@null*/OptionDescription getAssignedOption() ;

    /**
     * Expression assigned to the option {@code getAssignedOption} by this rule.
     *
     */
    public abstract RValueExpression assignedExpression() ;
}
