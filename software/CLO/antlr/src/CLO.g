
grammar CLO;

options {
  superClass=AbstractParser;
}

@header {
  package ie.ucd.clo.parser; 
}

@lexer::header {
  package ie.ucd.clo.parser;
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
arg_definition  :  (arg_name ':')? '{' '"' arg_alias '"' (',' '"' arg_alias '"')* '}' (':' param_definition)?
                ;

arg_name  :  NAME
          ;

arg_alias  :  possible_dash_started_name
           ;

param_definition  :  '{' NAME '}' 
                  ;

/**********************************************/

args_format_section  :  'TBD'  
                     ;

/**********************************************/

where_section  :  'TBD'
               ;

/**********************************************/

fly_section  :  'FLY::' (fly_rule)*
                   ;

fly_rule  :  NAME '->' NAME ':=' constant (',' NAME ':=' constant)* ';'
               ;

/**********************************************/

overrides_section  :  'OVERRIDES::' (override_rule)*
                   ;

override_rule  :  NAME comparison_op constant ('AND' NAME comparison_op constant)* '->' NAME ':=' constant ';'
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
