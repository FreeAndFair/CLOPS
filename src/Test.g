
grammar Test;

@header {
  package ie.ucd.clops.test;
  
  import java.util.LinkedList; 
}

@lexer::header {
  package ie.ucd.clops.test;
}

tests returns [List<TestSet> testSets]: 
  { $testSets = new LinkedList<TestSet>(); }
  (
    test_set { $testSets.add($test_set.set); }
  )+ 
  EOF
;

test_set returns [TestSet set]:
  test_file
  test_name
  test_cases 
  { $set = new TestSet($test_file.path, $test_name.name, $test_cases.cases); }
;

test_cases returns [List<TestCase> cases]:
  { $cases = new LinkedList<TestCase>(); }
  (
   test_case { $cases.add($test_case.testCase); }
  )+
;

test_case returns [TestCase testCase]: 
  condition ':'
  test_input
  { $testCase = new TestCase($condition.b, $test_input.testInput); }
;

condition returns [boolean b]:
    ( 'valid' { $b = true; } )
  | ( 'invalid' { $b = false; } )
;  

test_file returns [String path]:
  'file' ':' file
  { $path = $file.text; } 
;

test_input returns [String testInput]:
  b=UNCHECKED_CODE_BLOCK
  { $testInput = $b.text; }  
;

test_name returns [String name]:
  'name' ':' filestring
  { $name = $filestring.text; }
;
  

file : filestring ('/' filestring)*
     ;

filestring  :   ALPHANUMERIC ( ALPHANUMERIC | '-' | '_' | '.' )*
              | '.'
              | '..'
            ;

integer  : DIGIT+
         ;

UNCHECKED_CODE_BLOCK  :
  UNCHECKED_CODE { setText($text.substring(1, $text.length()-1).trim()); }
;
   
fragment                  
UNCHECKED_CODE :
  '{' 
  ( options {greedy=false; k=2;}
  : UNCHECKED_CODE
  | .
  )*
  '}'
;

ALPHANUMERIC  : ALPHA | DIGIT
              ;

fragment
ALPHA  : 'A'..'Z' | 'a'..'z'
       ;

fragment
DIGIT  : '0'..'9'
       ;

COMMENT  :  LINE_COMMENT+ { $channel=HIDDEN; }
         ;

fragment 
LINE_COMMENT  :  COMMENT_START (options {greedy=false;} : .)* NEWLINE 
              ;

fragment
COMMENT_START  : '//'
               ;

fragment
NEWLINE  :  '\r'? '\n' 
         ;

WHITESPACE  :  (' '|'\n'|'\r'|'\t')+ {$channel=HIDDEN;}
            ;