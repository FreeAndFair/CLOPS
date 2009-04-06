// $ANTLR 3.1.3 Mar 18, 2009 10:09:25 /home/fintan/workspace/clops/src/Test.g 2009-04-06 18:14:14

  package ie.ucd.clops.test;
  
  import java.util.LinkedList; 


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

public class TestParser extends Parser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "UNCHECKED_CODE_BLOCK", "ALPHANUMERIC", "DIGIT", "UNCHECKED_CODE", "ALPHA", "LINE_COMMENT", "COMMENT", "COMMENT_START", "NEWLINE", "WHITESPACE", "':'", "'valid'", "'invalid'", "'file'", "'name'", "'/'", "'-'", "'_'", "'.'", "'..'"
    };
    public static final int LINE_COMMENT=9;
    public static final int T__23=23;
    public static final int T__22=22;
    public static final int UNCHECKED_CODE_BLOCK=4;
    public static final int T__21=21;
    public static final int T__20=20;
    public static final int WHITESPACE=13;
    public static final int EOF=-1;
    public static final int COMMENT_START=11;
    public static final int ALPHA=8;
    public static final int UNCHECKED_CODE=7;
    public static final int T__19=19;
    public static final int T__16=16;
    public static final int T__15=15;
    public static final int NEWLINE=12;
    public static final int T__18=18;
    public static final int T__17=17;
    public static final int T__14=14;
    public static final int ALPHANUMERIC=5;
    public static final int DIGIT=6;
    public static final int COMMENT=10;

    // delegates
    // delegators


        public TestParser(TokenStream input) {
            this(input, new RecognizerSharedState());
        }
        public TestParser(TokenStream input, RecognizerSharedState state) {
            super(input, state);
             
        }
        

    public String[] getTokenNames() { return TestParser.tokenNames; }
    public String getGrammarFileName() { return "/home/fintan/workspace/clops/src/Test.g"; }



    // $ANTLR start "tests"
    // /home/fintan/workspace/clops/src/Test.g:14:1: tests returns [List<TestSet> testSets] : ( test_set )+ EOF ;
    public final List<TestSet> tests() throws RecognitionException {
        List<TestSet> testSets = null;

        TestSet test_set1 = null;


        try {
            // /home/fintan/workspace/clops/src/Test.g:14:39: ( ( test_set )+ EOF )
            // /home/fintan/workspace/clops/src/Test.g:15:3: ( test_set )+ EOF
            {
             testSets = new LinkedList<TestSet>(); 
            // /home/fintan/workspace/clops/src/Test.g:16:3: ( test_set )+
            int cnt1=0;
            loop1:
            do {
                int alt1=2;
                int LA1_0 = input.LA(1);

                if ( (LA1_0==17) ) {
                    alt1=1;
                }


                switch (alt1) {
            	case 1 :
            	    // /home/fintan/workspace/clops/src/Test.g:17:5: test_set
            	    {
            	    pushFollow(FOLLOW_test_set_in_tests42);
            	    test_set1=test_set();

            	    state._fsp--;

            	     testSets.add(test_set1); 

            	    }
            	    break;

            	default :
            	    if ( cnt1 >= 1 ) break loop1;
                        EarlyExitException eee =
                            new EarlyExitException(1, input);
                        throw eee;
                }
                cnt1++;
            } while (true);

            match(input,EOF,FOLLOW_EOF_in_tests54); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return testSets;
    }
    // $ANTLR end "tests"


    // $ANTLR start "test_set"
    // /home/fintan/workspace/clops/src/Test.g:22:1: test_set returns [TestSet set] : test_file test_name test_cases ;
    public final TestSet test_set() throws RecognitionException {
        TestSet set = null;

        String test_file2 = null;

        String test_name3 = null;

        List<TestCase> test_cases4 = null;


        try {
            // /home/fintan/workspace/clops/src/Test.g:22:31: ( test_file test_name test_cases )
            // /home/fintan/workspace/clops/src/Test.g:23:3: test_file test_name test_cases
            {
            pushFollow(FOLLOW_test_file_in_test_set68);
            test_file2=test_file();

            state._fsp--;

            pushFollow(FOLLOW_test_name_in_test_set72);
            test_name3=test_name();

            state._fsp--;

            pushFollow(FOLLOW_test_cases_in_test_set76);
            test_cases4=test_cases();

            state._fsp--;

             set = new TestSet(test_file2, test_name3, test_cases4); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return set;
    }
    // $ANTLR end "test_set"


    // $ANTLR start "test_cases"
    // /home/fintan/workspace/clops/src/Test.g:29:1: test_cases returns [List<TestCase> cases] : ( test_case )+ ;
    public final List<TestCase> test_cases() throws RecognitionException {
        List<TestCase> cases = null;

        TestCase test_case5 = null;


        try {
            // /home/fintan/workspace/clops/src/Test.g:29:42: ( ( test_case )+ )
            // /home/fintan/workspace/clops/src/Test.g:30:3: ( test_case )+
            {
             cases = new LinkedList<TestCase>(); 
            // /home/fintan/workspace/clops/src/Test.g:31:3: ( test_case )+
            int cnt2=0;
            loop2:
            do {
                int alt2=2;
                int LA2_0 = input.LA(1);

                if ( ((LA2_0>=15 && LA2_0<=16)) ) {
                    alt2=1;
                }


                switch (alt2) {
            	case 1 :
            	    // /home/fintan/workspace/clops/src/Test.g:32:4: test_case
            	    {
            	    pushFollow(FOLLOW_test_case_in_test_cases104);
            	    test_case5=test_case();

            	    state._fsp--;

            	     cases.add(test_case5); 

            	    }
            	    break;

            	default :
            	    if ( cnt2 >= 1 ) break loop2;
                        EarlyExitException eee =
                            new EarlyExitException(2, input);
                        throw eee;
                }
                cnt2++;
            } while (true);


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return cases;
    }
    // $ANTLR end "test_cases"


    // $ANTLR start "test_case"
    // /home/fintan/workspace/clops/src/Test.g:36:1: test_case returns [TestCase testCase] : condition ':' test_input ;
    public final TestCase test_case() throws RecognitionException {
        TestCase testCase = null;

        boolean condition6 = false;

        String test_input7 = null;


        try {
            // /home/fintan/workspace/clops/src/Test.g:36:38: ( condition ':' test_input )
            // /home/fintan/workspace/clops/src/Test.g:37:3: condition ':' test_input
            {
            pushFollow(FOLLOW_condition_in_test_case126);
            condition6=condition();

            state._fsp--;

            match(input,14,FOLLOW_14_in_test_case128); 
            pushFollow(FOLLOW_test_input_in_test_case132);
            test_input7=test_input();

            state._fsp--;

             testCase = new TestCase(condition6, test_input7); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return testCase;
    }
    // $ANTLR end "test_case"


    // $ANTLR start "condition"
    // /home/fintan/workspace/clops/src/Test.g:42:1: condition returns [boolean b] : ( ( 'valid' ) | ( 'invalid' ) );
    public final boolean condition() throws RecognitionException {
        boolean b = false;

        try {
            // /home/fintan/workspace/clops/src/Test.g:42:30: ( ( 'valid' ) | ( 'invalid' ) )
            int alt3=2;
            int LA3_0 = input.LA(1);

            if ( (LA3_0==15) ) {
                alt3=1;
            }
            else if ( (LA3_0==16) ) {
                alt3=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 3, 0, input);

                throw nvae;
            }
            switch (alt3) {
                case 1 :
                    // /home/fintan/workspace/clops/src/Test.g:43:5: ( 'valid' )
                    {
                    // /home/fintan/workspace/clops/src/Test.g:43:5: ( 'valid' )
                    // /home/fintan/workspace/clops/src/Test.g:43:7: 'valid'
                    {
                    match(input,15,FOLLOW_15_in_condition154); 
                     b = true; 

                    }


                    }
                    break;
                case 2 :
                    // /home/fintan/workspace/clops/src/Test.g:44:5: ( 'invalid' )
                    {
                    // /home/fintan/workspace/clops/src/Test.g:44:5: ( 'invalid' )
                    // /home/fintan/workspace/clops/src/Test.g:44:7: 'invalid'
                    {
                    match(input,16,FOLLOW_16_in_condition166); 
                     b = false; 

                    }


                    }
                    break;

            }
        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return b;
    }
    // $ANTLR end "condition"


    // $ANTLR start "test_file"
    // /home/fintan/workspace/clops/src/Test.g:47:1: test_file returns [String path] : 'file' ':' file ;
    public final String test_file() throws RecognitionException {
        String path = null;

        TestParser.file_return file8 = null;


        try {
            // /home/fintan/workspace/clops/src/Test.g:47:32: ( 'file' ':' file )
            // /home/fintan/workspace/clops/src/Test.g:48:3: 'file' ':' file
            {
            match(input,17,FOLLOW_17_in_test_file186); 
            match(input,14,FOLLOW_14_in_test_file188); 
            pushFollow(FOLLOW_file_in_test_file190);
            file8=file();

            state._fsp--;

             path = (file8!=null?input.toString(file8.start,file8.stop):null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return path;
    }
    // $ANTLR end "test_file"


    // $ANTLR start "test_input"
    // /home/fintan/workspace/clops/src/Test.g:52:1: test_input returns [String testInput] : b= UNCHECKED_CODE_BLOCK ;
    public final String test_input() throws RecognitionException {
        String testInput = null;

        Token b=null;

        try {
            // /home/fintan/workspace/clops/src/Test.g:52:38: (b= UNCHECKED_CODE_BLOCK )
            // /home/fintan/workspace/clops/src/Test.g:53:3: b= UNCHECKED_CODE_BLOCK
            {
            b=(Token)match(input,UNCHECKED_CODE_BLOCK,FOLLOW_UNCHECKED_CODE_BLOCK_in_test_input211); 
             testInput = (b!=null?b.getText():null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return testInput;
    }
    // $ANTLR end "test_input"


    // $ANTLR start "test_name"
    // /home/fintan/workspace/clops/src/Test.g:57:1: test_name returns [String name] : 'name' ':' filestring ;
    public final String test_name() throws RecognitionException {
        String name = null;

        TestParser.filestring_return filestring9 = null;


        try {
            // /home/fintan/workspace/clops/src/Test.g:57:32: ( 'name' ':' filestring )
            // /home/fintan/workspace/clops/src/Test.g:58:3: 'name' ':' filestring
            {
            match(input,18,FOLLOW_18_in_test_name231); 
            match(input,14,FOLLOW_14_in_test_name233); 
            pushFollow(FOLLOW_filestring_in_test_name235);
            filestring9=filestring();

            state._fsp--;

             name = (filestring9!=null?input.toString(filestring9.start,filestring9.stop):null); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return name;
    }
    // $ANTLR end "test_name"

    public static class file_return extends ParserRuleReturnScope {
    };

    // $ANTLR start "file"
    // /home/fintan/workspace/clops/src/Test.g:63:1: file : filestring ( '/' filestring )* ;
    public final TestParser.file_return file() throws RecognitionException {
        TestParser.file_return retval = new TestParser.file_return();
        retval.start = input.LT(1);

        try {
            // /home/fintan/workspace/clops/src/Test.g:63:6: ( filestring ( '/' filestring )* )
            // /home/fintan/workspace/clops/src/Test.g:63:8: filestring ( '/' filestring )*
            {
            pushFollow(FOLLOW_filestring_in_file251);
            filestring();

            state._fsp--;

            // /home/fintan/workspace/clops/src/Test.g:63:19: ( '/' filestring )*
            loop4:
            do {
                int alt4=2;
                int LA4_0 = input.LA(1);

                if ( (LA4_0==19) ) {
                    alt4=1;
                }


                switch (alt4) {
            	case 1 :
            	    // /home/fintan/workspace/clops/src/Test.g:63:20: '/' filestring
            	    {
            	    match(input,19,FOLLOW_19_in_file254); 
            	    pushFollow(FOLLOW_filestring_in_file256);
            	    filestring();

            	    state._fsp--;


            	    }
            	    break;

            	default :
            	    break loop4;
                }
            } while (true);


            }

            retval.stop = input.LT(-1);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end "file"

    public static class filestring_return extends ParserRuleReturnScope {
    };

    // $ANTLR start "filestring"
    // /home/fintan/workspace/clops/src/Test.g:66:1: filestring : ( ALPHANUMERIC ( ALPHANUMERIC | '-' | '_' | '.' )* | '.' | '..' );
    public final TestParser.filestring_return filestring() throws RecognitionException {
        TestParser.filestring_return retval = new TestParser.filestring_return();
        retval.start = input.LT(1);

        try {
            // /home/fintan/workspace/clops/src/Test.g:66:13: ( ALPHANUMERIC ( ALPHANUMERIC | '-' | '_' | '.' )* | '.' | '..' )
            int alt6=3;
            switch ( input.LA(1) ) {
            case ALPHANUMERIC:
                {
                alt6=1;
                }
                break;
            case 22:
                {
                alt6=2;
                }
                break;
            case 23:
                {
                alt6=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 6, 0, input);

                throw nvae;
            }

            switch (alt6) {
                case 1 :
                    // /home/fintan/workspace/clops/src/Test.g:66:17: ALPHANUMERIC ( ALPHANUMERIC | '-' | '_' | '.' )*
                    {
                    match(input,ALPHANUMERIC,FOLLOW_ALPHANUMERIC_in_filestring275); 
                    // /home/fintan/workspace/clops/src/Test.g:66:30: ( ALPHANUMERIC | '-' | '_' | '.' )*
                    loop5:
                    do {
                        int alt5=2;
                        int LA5_0 = input.LA(1);

                        if ( (LA5_0==ALPHANUMERIC||(LA5_0>=20 && LA5_0<=22)) ) {
                            alt5=1;
                        }


                        switch (alt5) {
                    	case 1 :
                    	    // /home/fintan/workspace/clops/src/Test.g:
                    	    {
                    	    if ( input.LA(1)==ALPHANUMERIC||(input.LA(1)>=20 && input.LA(1)<=22) ) {
                    	        input.consume();
                    	        state.errorRecovery=false;
                    	    }
                    	    else {
                    	        MismatchedSetException mse = new MismatchedSetException(null,input);
                    	        throw mse;
                    	    }


                    	    }
                    	    break;

                    	default :
                    	    break loop5;
                        }
                    } while (true);


                    }
                    break;
                case 2 :
                    // /home/fintan/workspace/clops/src/Test.g:67:17: '.'
                    {
                    match(input,22,FOLLOW_22_in_filestring312); 

                    }
                    break;
                case 3 :
                    // /home/fintan/workspace/clops/src/Test.g:68:17: '..'
                    {
                    match(input,23,FOLLOW_23_in_filestring330); 

                    }
                    break;

            }
            retval.stop = input.LT(-1);

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return retval;
    }
    // $ANTLR end "filestring"


    // $ANTLR start "integer"
    // /home/fintan/workspace/clops/src/Test.g:71:1: integer : ( DIGIT )+ ;
    public final void integer() throws RecognitionException {
        try {
            // /home/fintan/workspace/clops/src/Test.g:71:10: ( ( DIGIT )+ )
            // /home/fintan/workspace/clops/src/Test.g:71:12: ( DIGIT )+
            {
            // /home/fintan/workspace/clops/src/Test.g:71:12: ( DIGIT )+
            int cnt7=0;
            loop7:
            do {
                int alt7=2;
                int LA7_0 = input.LA(1);

                if ( (LA7_0==DIGIT) ) {
                    alt7=1;
                }


                switch (alt7) {
            	case 1 :
            	    // /home/fintan/workspace/clops/src/Test.g:71:12: DIGIT
            	    {
            	    match(input,DIGIT,FOLLOW_DIGIT_in_integer352); 

            	    }
            	    break;

            	default :
            	    if ( cnt7 >= 1 ) break loop7;
                        EarlyExitException eee =
                            new EarlyExitException(7, input);
                        throw eee;
                }
                cnt7++;
            } while (true);


            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "integer"

    // Delegated rules


 

    public static final BitSet FOLLOW_test_set_in_tests42 = new BitSet(new long[]{0x0000000000020000L});
    public static final BitSet FOLLOW_EOF_in_tests54 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_test_file_in_test_set68 = new BitSet(new long[]{0x0000000000040000L});
    public static final BitSet FOLLOW_test_name_in_test_set72 = new BitSet(new long[]{0x0000000000018000L});
    public static final BitSet FOLLOW_test_cases_in_test_set76 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_test_case_in_test_cases104 = new BitSet(new long[]{0x0000000000018002L});
    public static final BitSet FOLLOW_condition_in_test_case126 = new BitSet(new long[]{0x0000000000004000L});
    public static final BitSet FOLLOW_14_in_test_case128 = new BitSet(new long[]{0x0000000000000010L});
    public static final BitSet FOLLOW_test_input_in_test_case132 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_15_in_condition154 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_16_in_condition166 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_17_in_test_file186 = new BitSet(new long[]{0x0000000000004000L});
    public static final BitSet FOLLOW_14_in_test_file188 = new BitSet(new long[]{0x0000000000C00020L});
    public static final BitSet FOLLOW_file_in_test_file190 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_UNCHECKED_CODE_BLOCK_in_test_input211 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_18_in_test_name231 = new BitSet(new long[]{0x0000000000004000L});
    public static final BitSet FOLLOW_14_in_test_name233 = new BitSet(new long[]{0x0000000000C00020L});
    public static final BitSet FOLLOW_filestring_in_test_name235 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_filestring_in_file251 = new BitSet(new long[]{0x0000000000080002L});
    public static final BitSet FOLLOW_19_in_file254 = new BitSet(new long[]{0x0000000000C00020L});
    public static final BitSet FOLLOW_filestring_in_file256 = new BitSet(new long[]{0x0000000000080002L});
    public static final BitSet FOLLOW_ALPHANUMERIC_in_filestring275 = new BitSet(new long[]{0x0000000000700022L});
    public static final BitSet FOLLOW_set_in_filestring277 = new BitSet(new long[]{0x0000000000700022L});
    public static final BitSet FOLLOW_22_in_filestring312 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_23_in_filestring330 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_DIGIT_in_integer352 = new BitSet(new long[]{0x0000000000000042L});

}