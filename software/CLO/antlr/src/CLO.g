
grammar CLO;

options {
  superClass=AbstractParser;
}

@header {
  package ie.ucd.clo.dsl.parser; 
  
  import ie.ucd.clo.dsl.structs.OptionDescription;
  import ie.ucd.clo.dsl.structs.BasicOptionDescription;
  import ie.ucd.clo.dsl.OptionTypeFactory;
  import ie.ucd.clo.dsl.DSLParseException;
  
  import ie.ucd.clo.dsl.DSLParseException;
  
  import ie.ucd.clo.runtime.options.OptionType;
    
}

@lexer::header {
  package ie.ucd.clo.dsl.parser;
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

clo_specification  :  args_section
                      args_format_section
                      where_section
                      fly_section
                      overrides_section
                      validity_section
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
                   '{' '"' a1=arg_alias '"' 
                   { option.addAlias($a1.text); }
                   (',' '"' a=arg_alias '"'
                    { option.addAlias($a.text); }
                   )* 
                   '}'  
                   ( ':' '{' t=NAME '}'
                       { OptionType optionType = getOptionTypeFactory().getOptionType($t.text); option.setType(optionType); }
                     )? 
                   { System.out.println("Parsed option: " + option); }
                ;
                catch [DSLParseException e] {
                  System.out.println("Here.");
                  setCustomErrorMessage(e.toString());
                  throw new RecognitionException();
                } 
                catch [RecognitionException re] {
                  System.out.println("Here2.");
                  reportError(re);
                  recover(input,re);
                }

arg_name  :  NAME
          ;

arg_alias  :  possible_dash_started_name
           ;

/**********************************************/

args_format_section  :  'FORMAT::' format_clause  ';'
                     ;

format_clause  :  format_subclause
               ;

format_subclause  :  (   NAME  
                       | ( '(' format_subclause ')' )
                     ) 
                     (repitition_operator)?
                     (or_format_subclause)?
                  ;

or_format_subclause  :  ('OR')? format_subclause
                     ;

repitition_operator  : '*' | '+' | '?'
                    ;


/**********************************************/

where_section  :  'WHERE::' (where_clause)*
               ;

where_clause  :  NAME ':' NAME  ('OR' NAME)* ';'
              ;

/**********************************************/

fly_section  :  'FLY::' (fly_rule)*
                   ;

fly_rule  :  NAME '->' NAME ':=' constant (',' NAME ':=' constant)* ';'
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

possible_dash_started_name  :  (DASH DASH?)? NAME
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

//Standard name
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
