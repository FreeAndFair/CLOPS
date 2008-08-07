
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

clo_specification  :  'a'
                   ;
