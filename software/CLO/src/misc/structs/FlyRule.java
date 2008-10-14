package ie.ucd.clops.dsl.structs;

public abstract class FlyRule {

    /**
     * The option associated with this rule.
     *
     */
    public abstract OptionDescription getTriggeringOption() ;


   /**
     * Value under which the rule is triggered.
     *
     */
    public abstract RValueExpression triggeringExpression() ;


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