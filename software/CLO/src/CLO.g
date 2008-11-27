
grammar CLO;

options {
  superClass=AbstractParser;
}

@header {
  package ie.ucd.clops.dsl.parser; 
  
  import ie.ucd.clops.dsl.structs.OptionDescription;
  import ie.ucd.clops.dsl.structs.OptionGroupDescription;
  import ie.ucd.clops.dsl.structs.BasicOptionDescription;
  import ie.ucd.clops.dsl.structs.FlyRuleDescription;
  import ie.ucd.clops.dsl.structs.AssignmentDescription;
  import ie.ucd.clops.dsl.OptionTypeFactory;
  import ie.ucd.clops.dsl.OptionType;
  import ie.ucd.clops.dsl.UnknownOptionTypeException;
  import ie.ucd.clops.dsl.parser.DSLParseException;
}

@lexer::header {
  package ie.ucd.clops.dsl.parser;
}

@members {
  //Currently nothing
}

/**********************************************  
 ##############################################
 ###   Parser...                            ###
 ##############################################
 **********************************************/

prog  :  clo_specification EOF         
      ;

clo_specification  :  name_section
                      (package_section)?
                      args_section
                      args_format_section
                      where_section
                      fly_section
                      overrides_section
                      validity_section
                   ;

/**********************************************/

name_section  :  'NAME::'
                 NAME
                 { getDslInformation().setParserName($NAME.text); }
              ;

/**********************************************/

package_section  :  'PACKAGE::'
                    package_name
                    { getDslInformation().setPackageName($package_name.text); }
              ;
              
package_name  :  NAME ('.' NAME)*
              ;


/**********************************************/

args_section  :  'ARGS::'
                 (arg_definition)+
              ;

//Currently allowing anything for the 
arg_definition  
@init { OptionDescription option = new BasicOptionDescription(); }
                :  id=arg_name ':'
                   { option.setId($id.text); } 
                   '{'
                   ( 
                     a1=arg_regexp 
                     { option.addPrefixRegexp(stripStringMarks($a1.text)); }
                     (',' a=arg_regexp
                      { option.addPrefixRegexp(stripStringMarks($a.text)); }
                     )* 
                   )?
                   '}'
                   (
                   ( ':' '{' t=NAME '}'
                       { try { OptionType optionType = getOptionTypeFactory().getOptionType($t.text); option.setType(optionType);
                             } catch(UnknownOptionTypeException e) { throw new DSLParseException(e.getMessage()); } 
                       }
                   )
                   |
                       { OptionType optionType = getOptionTypeFactory().getDefaultOptionType(); option.setType(optionType); }
                   ) 
                   ( ':' '['
                     pn1=property_name  
                     ( '=' pv1=property_value
                       { option.setProperty($pn1.text, stripStringMarks($pv1.text)); }
                      |
                       { option.setProperty($pn1.text, "true"); }
                     )
                     ( ',' pn=property_name 
                       ( '=' pv=property_value
                         { option.setProperty($pn.text, stripStringMarks($pv.text)); }
                        |
                         { option.setProperty($pn.text, "true"); }
                       ) 
                     )*
                     ']' 
                   )?
                     
                   { getDslInformation().addOptionDescription(option); }
                ;
                catch [DSLParseException e] {
                  setCustomErrorMessage(e.toString());
                  throw new RecognitionException();
                } 
                catch [RecognitionException re] {
                  reportError(re);
                  recover(input,re);
                }

arg_name  :  NAME
          ;

arg_regexp  :  string_constant
            ;
           
property_name  :  NAME
               ;
               
property_value  :  string_constant
                ;

/**********************************************/

args_format_section  :  'FORMAT::' format_clause  
                        { getDslInformation().setFormatString($format_clause.text); }
                        ';'
                     ;

format_clause  :  format_subclause
               ;

format_subclause  :  (   NAME  
                       | ( '(' format_subclause ')' )
                     ) 
                     (repitition_operator)?
                     (or_format_subclause)?
                  ;

or_format_subclause  :  ('|')? format_subclause
                     ;

repitition_operator  : '*' | '+' | '?'
                    ;


/**********************************************/

where_section  :  'WHERE::' (where_clause)*
               ;

where_clause  :  group=NAME
                 { OptionGroupDescription opGroup = new OptionGroupDescription($group.text); } 
                 ':' child1=NAME
                 { opGroup.addChild($child1.text); }  
                 ('OR' child=NAME { opGroup.addChild($child.text); } )* 
                 { getDslInformation().addOptionGroupDescription(opGroup); }
                 ';'
              ;

/**********************************************/

fly_section  :  'FLY::' (fly_rule)*
             ;

fly_rule  :  t=NAME
             { FlyRuleDescription or = new FlyRuleDescription($t.text); } 
             '->' n1=NAME ':=' v1=constant
             { or.addAssignment(new AssignmentDescription($n1.text, $v1.text)); } 
             (',' 
              n=NAME ':=' v=constant
              { or.addAssignment(new AssignmentDescription($n.text, $v.text)); }
             )* ';'
             { getDslInformation().addFlyRuleDescription(or); }
          ;

/**********************************************/

overrides_section  :  'OVERRIDES::' (override_rule)*
                   ;

override_rule  :  NAME comparison_op constant ('AND' NAME comparison_op constant)* '->' NAME ':=' constant (',' NAME ':=' constant)* ';'
               ;

/**********************************************/

validity_section  :  'VALIDITY::' (validity_rule)*
                  ;

validity_rule  :  NAME comparison_op constant ('OR' NAME comparison_op constant)* ';'
               ;

/**********************************************
 **********************************************/

constant  :    boolean_constant
             | integer_constant  
             | string_constant
             | unspecified_constant
          ;

boolean_constant  :  'true' | 'false'
                  ;

integer_constant  :  INTEGER
                  ;

string_constant  :  '"' .* '"'
                 ;

unspecified_constant  :  '?'
                      ;

//Zero, one or two dashes, followed by an identifier that may start with a digit.
possible_dash_started_alias  :  (DASH DASH?)? alias
                             ;
                            
alias  :  ( NAME | INTEGER)+
       ;

/**********************************************/

comparison_op  :    '='
                  | '!='
                  | '>'
                  | '<'
                  | '<='
                  | '>='
               ;

/**********************************************  
 ##############################################
 ###   Lexer...                             ###
 ##############################################
 **********************************************/ 

MULTI_LINE_COMMENT  :  '/*' .* '*/' { $channel=HIDDEN; }
                    ;

SINGLE_LINE_COMMENT  :  '//' .* NEWLINE  { $channel=HIDDEN; }
                     ;

fragment
NEWLINE  :  '\r'? '\n' 
         ;

/**********************************************/

//  : DIGIT  ( ALPHANUMERIC | UNDERSCORE | DASH )*
//                   ;

//Identifier name
NAME  : ALPHA ( ALPHANUMERIC | UNDERSCORE | DASH )*
      ;
                                    
fragment 
UNDERSCORE  :  '_' 
            ;

DASH  :  '-'
      ;
                    
fragment 
ALPHANUMERIC  :  ALPHA | DIGIT 
              ;
               
INTEGER  :  (DIGIT)+ 
         ;
         
REAL  :  DIGIT+ '.' DIGIT+ 
      ;
      
fragment 
DIGIT  :  '0'..'9' 
       ;
  
fragment 
ALPHA  : LOWER | UPPER 
       ;
                
fragment 
LOWER  : 'a'..'z' 
       ;
                
fragment 
UPPER  : 'A'..'Z' 
       ;

/**********************************************  
 ***   Whitespace                           ***
 **********************************************/
 
WHITESPACE  :  (' '|'\n'|'\r'|'\t')+ {$channel=HIDDEN;}
            ;
