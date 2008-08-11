
grammar CLO;

//options {
//}

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
                      defaults_section
                      overrides_section
                      validity_section
                   ;

/**********************************************/

args_section  :  'ARGS::'
                 (arg_definition)+
              ;

arg_definition  :  '[' (arg_name ':')? '{' '"' a1=arg_alias '"' (',' '"' a=arg_alias '"')* '}' (':' param_definition)? ']'
                ;

arg_name  :  NAME
          ;

arg_alias  :  NAME
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

defaults_section  :  'DEFAULTS::' (default_rule)*
                  ;

default_rule  :  'TBD' '->' 'TBD'
              ;

/**********************************************/

overrides_section  :  'OVERRIDES::' (override_rule)*
                   ;

override_rule  :  'TBD' '->' 'TBD'
               ;

/**********************************************/

validity_section  :  'VALIDITY::' (validity_rule)*
                  ;

validity_rule  :  'TBD' '->' 'TBD'
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
NAME  : ( ALPHANUMERIC_UNDERSCORE_OR_DASH )+
      ;

fragment 
ALPHANUMERIC_UNDERSCORE_OR_DASH  : ALPHANUMERIC | UNDERSCORE | DASH 
                                 ;
                                     
fragment 
UNDERSCORE  :  '_' 
            ;

fragment 
DASH  :  '-'
      ;
                    
fragment 
ALPHANUMERIC  :  ALPHA | DIGIT 
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
