/**
 * COMMANDO - Generalized parsing of command line options
 *
 * Copyright (c) 2008 Dermot Cochran
 *
 * Permission is hereby granted, free of charge, to any person obtaining a copy
 * of this software and associated documentation files (the "Software"), to deal
 * in the Software without restriction, including without limitation the rights
 * to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
 * copies of the Software, and to permit persons to whom the Software is
 * furnished to do so, subject to the following conditions:
 *
 * The above copyright notice and this permission notice shall be included in
 * all copies or substantial portions of the Software.
 *
 * THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
 * IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
 * FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
 * AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
 * LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
 * OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN
 * THE SOFTWARE.
 */

package commando.dependencies;

/**
 * <BON>
 * class_chart RULE
 * indexing
 *   created: "2008-08-13-dc";
 *   revised: "2008-10-14-dc";
 *   level_of_detail: "0";
 *   in_cluster: "DEPENDENCIES"
 * explanation
 *   "An expression in which the LHS is set of options values and the RHS is a single assignment of a new option value"
 * query
 *   "What is my left-hand-side (source) expression?",
 *   "What is my right-hand-side (target) expression?"
 * command
 *   "Set target option",
 *   "Set target value",
 *   "Add to left hand side expression"
 * end
 * </BON>
 */

public class Rule {
	/**
	 * <BON>
	 * class_chart EXPRESSION
     * indexing
     *   created: "2008-11-12-dc";
     *   level_of_detail: "1";
     * explanation
     *  "Set of option value pairs"
     * inherit
     *   OPTION_VALUE_PAIR_SET
     * query
     *  "Which option value pairs do I contain?"
     * command
     *  "Add an option value pair"
     * constraint
     *  "Values must be compatible with the type and range of the option"
     * end
	 * </BON>
	 */
	public class Expression {
		//@ model OptionValuePair[] optionValuePairs;
		
		/**
		 * 
		 */
		public void addOptionValuePair();
	}
	
	/**
	 * <BON>
	 * class_chart ASSIGNMENT_EXPRESSION
     * indexing
     *   created: "2008-11-12-dc";
     *   level_of_detail: "1"
     * explanation
     * "Single assignment of a new value to an option"
     * inherit
     *   OPTION_VALUE_PAIR
     * query
     *   "Which option is to be set?",
     *   "Which value is to be set?"
     * command
     *   "Assign value to option"
     * end
	 * </BON>
	 */
	public class AssignmentExpression extends OptionValuePair {	
		
		/**
		 * Assign a value to an option.
		 * 
		 * <JML>
		 * ensures \result.getValue().equals(value);
		 * ensures \result.isSame(option);
		 * </JML>
		 */
		Option assign (/*@ non_null @*/ Option option, /*@ non_null @*/ Value value);
	}
	
	/**
	 * class_chart OPTION_VALUE_PAIR
     * indexing
     *   created: "2008-11-12-dc";
     *   alias: "pair of OPTION and VALUE";
     *   level_of_detail: "1"
     * explanation
     *   "The relationship between options and values"
     * query
     *   "What is my value?",
     *   "Which option do I refer to?"
     * command
     *   "Set my value?",
     *   "Choose an option"
     * end
	 */
	public class OptionValuePair {
		Option option;
		Value value;
		
		/**
		 * <JML>
		 * ensures \result.equals(option);
		 * </JML>
		 */
        public Option getOption();
        
        /**
         * <JML>
         * ensures \result.equals(value);
         * </JML>
         */
        public Value getValue();
	}
	
	//@ model Expression leftHandSide;
    //@ model AssignmentExpression rightHandSide;
	
	/**
	 * Reveal the left hand side of the rule.
	 * 
	 * <JML>
	 * </JML>
	 */
	public Expression getLeftHandSide();
	
	/**
	 * Reveal the right hand side of the rule.
	 * 
	 * <JML>
	 * </JML>
	 */
	public AssignmentExpression getRightHandSide();
	
	/**
	 * <JML>
	 * ensures getRightHandSide().getOption().equals(options);
	 * </JML>
	 */
	public void setTargetOption(Option option);
	
	/**
	 * <JML>
	 * ensures getRightHandSide().getValue().equals(value);
	 * </JML>
	 */
	public void setTargetValue(Value value);
	
	/**
	 * Add an option value pair to the LHS of the rule.
	 * 
	 * <JML>
	 * ensures getLeftHandSide().contains(optionValuePair);
	 * </JML>
	 */
	public void addToLeftHandSideExpression(OptionValuePair optionValuePair);
}