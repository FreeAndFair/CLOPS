// $ANTLR 3.1.3 Mar 18, 2009 10:09:25 /Users/fintan/workspace/clops/src/Test.g 2009-05-08 14:39:43

  package ie.ucd.clops.test;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

public class TestLexer extends Lexer {
    public static final int LINE_COMMENT=9;
    public static final int T__23=23;
    public static final int UNCHECKED_CODE_BLOCK=4;
    public static final int T__22=22;
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

    public TestLexer() {;} 
    public TestLexer(CharStream input) {
        this(input, new RecognizerSharedState());
    }
    public TestLexer(CharStream input, RecognizerSharedState state) {
        super(input,state);

    }
    public String getGrammarFileName() { return "/Users/fintan/workspace/clops/src/Test.g"; }

    // $ANTLR start "T__14"
    public final void mT__14() throws RecognitionException {
        try {
            int _type = T__14;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/Test.g:7:7: ( ':' )
            // /Users/fintan/workspace/clops/src/Test.g:7:9: ':'
            {
            match(':'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__14"

    // $ANTLR start "T__15"
    public final void mT__15() throws RecognitionException {
        try {
            int _type = T__15;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/Test.g:8:7: ( 'valid' )
            // /Users/fintan/workspace/clops/src/Test.g:8:9: 'valid'
            {
            match("valid"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__15"

    // $ANTLR start "T__16"
    public final void mT__16() throws RecognitionException {
        try {
            int _type = T__16;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/Test.g:9:7: ( 'invalid' )
            // /Users/fintan/workspace/clops/src/Test.g:9:9: 'invalid'
            {
            match("invalid"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__16"

    // $ANTLR start "T__17"
    public final void mT__17() throws RecognitionException {
        try {
            int _type = T__17;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/Test.g:10:7: ( 'file' )
            // /Users/fintan/workspace/clops/src/Test.g:10:9: 'file'
            {
            match("file"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__17"

    // $ANTLR start "T__18"
    public final void mT__18() throws RecognitionException {
        try {
            int _type = T__18;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/Test.g:11:7: ( 'name' )
            // /Users/fintan/workspace/clops/src/Test.g:11:9: 'name'
            {
            match("name"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__18"

    // $ANTLR start "T__19"
    public final void mT__19() throws RecognitionException {
        try {
            int _type = T__19;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/Test.g:12:7: ( '/' )
            // /Users/fintan/workspace/clops/src/Test.g:12:9: '/'
            {
            match('/'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__19"

    // $ANTLR start "T__20"
    public final void mT__20() throws RecognitionException {
        try {
            int _type = T__20;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/Test.g:13:7: ( '-' )
            // /Users/fintan/workspace/clops/src/Test.g:13:9: '-'
            {
            match('-'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__20"

    // $ANTLR start "T__21"
    public final void mT__21() throws RecognitionException {
        try {
            int _type = T__21;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/Test.g:14:7: ( '_' )
            // /Users/fintan/workspace/clops/src/Test.g:14:9: '_'
            {
            match('_'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__21"

    // $ANTLR start "T__22"
    public final void mT__22() throws RecognitionException {
        try {
            int _type = T__22;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/Test.g:15:7: ( '.' )
            // /Users/fintan/workspace/clops/src/Test.g:15:9: '.'
            {
            match('.'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__22"

    // $ANTLR start "T__23"
    public final void mT__23() throws RecognitionException {
        try {
            int _type = T__23;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/Test.g:16:7: ( '..' )
            // /Users/fintan/workspace/clops/src/Test.g:16:9: '..'
            {
            match(".."); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__23"

    // $ANTLR start "UNCHECKED_CODE_BLOCK"
    public final void mUNCHECKED_CODE_BLOCK() throws RecognitionException {
        try {
            int _type = UNCHECKED_CODE_BLOCK;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/Test.g:82:23: ( UNCHECKED_CODE )
            // /Users/fintan/workspace/clops/src/Test.g:83:3: UNCHECKED_CODE
            {
            mUNCHECKED_CODE(); 
             setText(getText().substring(1, getText().length()-1).trim()); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "UNCHECKED_CODE_BLOCK"

    // $ANTLR start "UNCHECKED_CODE"
    public final void mUNCHECKED_CODE() throws RecognitionException {
        try {
            // /Users/fintan/workspace/clops/src/Test.g:87:16: ( '{' ( options {greedy=false; k=2; } : UNCHECKED_CODE | . )* '}' )
            // /Users/fintan/workspace/clops/src/Test.g:88:3: '{' ( options {greedy=false; k=2; } : UNCHECKED_CODE | . )* '}'
            {
            match('{'); 
            // /Users/fintan/workspace/clops/src/Test.g:89:3: ( options {greedy=false; k=2; } : UNCHECKED_CODE | . )*
            loop1:
            do {
                int alt1=3;
                int LA1_0 = input.LA(1);

                if ( (LA1_0=='}') ) {
                    alt1=3;
                }
                else if ( (LA1_0=='{') ) {
                    alt1=1;
                }
                else if ( ((LA1_0>='\u0000' && LA1_0<='z')||LA1_0=='|'||(LA1_0>='~' && LA1_0<='\uFFFF')) ) {
                    alt1=2;
                }


                switch (alt1) {
            	case 1 :
            	    // /Users/fintan/workspace/clops/src/Test.g:90:5: UNCHECKED_CODE
            	    {
            	    mUNCHECKED_CODE(); 

            	    }
            	    break;
            	case 2 :
            	    // /Users/fintan/workspace/clops/src/Test.g:91:5: .
            	    {
            	    matchAny(); 

            	    }
            	    break;

            	default :
            	    break loop1;
                }
            } while (true);

            match('}'); 

            }

        }
        finally {
        }
    }
    // $ANTLR end "UNCHECKED_CODE"

    // $ANTLR start "ALPHANUMERIC"
    public final void mALPHANUMERIC() throws RecognitionException {
        try {
            int _type = ALPHANUMERIC;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/Test.g:96:15: ( ALPHA | DIGIT )
            // /Users/fintan/workspace/clops/src/Test.g:
            {
            if ( (input.LA(1)>='0' && input.LA(1)<='9')||(input.LA(1)>='A' && input.LA(1)<='Z')||(input.LA(1)>='a' && input.LA(1)<='z') ) {
                input.consume();

            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;}


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "ALPHANUMERIC"

    // $ANTLR start "ALPHA"
    public final void mALPHA() throws RecognitionException {
        try {
            // /Users/fintan/workspace/clops/src/Test.g:100:8: ( 'A' .. 'Z' | 'a' .. 'z' )
            // /Users/fintan/workspace/clops/src/Test.g:
            {
            if ( (input.LA(1)>='A' && input.LA(1)<='Z')||(input.LA(1)>='a' && input.LA(1)<='z') ) {
                input.consume();

            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                recover(mse);
                throw mse;}


            }

        }
        finally {
        }
    }
    // $ANTLR end "ALPHA"

    // $ANTLR start "DIGIT"
    public final void mDIGIT() throws RecognitionException {
        try {
            // /Users/fintan/workspace/clops/src/Test.g:104:8: ( '0' .. '9' )
            // /Users/fintan/workspace/clops/src/Test.g:104:10: '0' .. '9'
            {
            matchRange('0','9'); 

            }

        }
        finally {
        }
    }
    // $ANTLR end "DIGIT"

    // $ANTLR start "COMMENT"
    public final void mCOMMENT() throws RecognitionException {
        try {
            int _type = COMMENT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/Test.g:107:10: ( ( LINE_COMMENT )+ )
            // /Users/fintan/workspace/clops/src/Test.g:107:13: ( LINE_COMMENT )+
            {
            // /Users/fintan/workspace/clops/src/Test.g:107:13: ( LINE_COMMENT )+
            int cnt2=0;
            loop2:
            do {
                int alt2=2;
                int LA2_0 = input.LA(1);

                if ( (LA2_0=='/') ) {
                    alt2=1;
                }


                switch (alt2) {
            	case 1 :
            	    // /Users/fintan/workspace/clops/src/Test.g:107:13: LINE_COMMENT
            	    {
            	    mLINE_COMMENT(); 

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

             _channel=HIDDEN; 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "COMMENT"

    // $ANTLR start "LINE_COMMENT"
    public final void mLINE_COMMENT() throws RecognitionException {
        try {
            // /Users/fintan/workspace/clops/src/Test.g:111:15: ( COMMENT_START ( options {greedy=false; } : . )* NEWLINE )
            // /Users/fintan/workspace/clops/src/Test.g:111:18: COMMENT_START ( options {greedy=false; } : . )* NEWLINE
            {
            mCOMMENT_START(); 
            // /Users/fintan/workspace/clops/src/Test.g:111:32: ( options {greedy=false; } : . )*
            loop3:
            do {
                int alt3=2;
                int LA3_0 = input.LA(1);

                if ( (LA3_0=='\r') ) {
                    alt3=2;
                }
                else if ( (LA3_0=='\n') ) {
                    alt3=2;
                }
                else if ( ((LA3_0>='\u0000' && LA3_0<='\t')||(LA3_0>='\u000B' && LA3_0<='\f')||(LA3_0>='\u000E' && LA3_0<='\uFFFF')) ) {
                    alt3=1;
                }


                switch (alt3) {
            	case 1 :
            	    // /Users/fintan/workspace/clops/src/Test.g:111:59: .
            	    {
            	    matchAny(); 

            	    }
            	    break;

            	default :
            	    break loop3;
                }
            } while (true);

            mNEWLINE(); 

            }

        }
        finally {
        }
    }
    // $ANTLR end "LINE_COMMENT"

    // $ANTLR start "COMMENT_START"
    public final void mCOMMENT_START() throws RecognitionException {
        try {
            // /Users/fintan/workspace/clops/src/Test.g:115:16: ( '//' )
            // /Users/fintan/workspace/clops/src/Test.g:115:18: '//'
            {
            match("//"); 


            }

        }
        finally {
        }
    }
    // $ANTLR end "COMMENT_START"

    // $ANTLR start "NEWLINE"
    public final void mNEWLINE() throws RecognitionException {
        try {
            // /Users/fintan/workspace/clops/src/Test.g:119:10: ( ( '\\r' )? '\\n' )
            // /Users/fintan/workspace/clops/src/Test.g:119:13: ( '\\r' )? '\\n'
            {
            // /Users/fintan/workspace/clops/src/Test.g:119:13: ( '\\r' )?
            int alt4=2;
            int LA4_0 = input.LA(1);

            if ( (LA4_0=='\r') ) {
                alt4=1;
            }
            switch (alt4) {
                case 1 :
                    // /Users/fintan/workspace/clops/src/Test.g:119:13: '\\r'
                    {
                    match('\r'); 

                    }
                    break;

            }

            match('\n'); 

            }

        }
        finally {
        }
    }
    // $ANTLR end "NEWLINE"

    // $ANTLR start "WHITESPACE"
    public final void mWHITESPACE() throws RecognitionException {
        try {
            int _type = WHITESPACE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/Test.g:122:13: ( ( ' ' | '\\n' | '\\r' | '\\t' )+ )
            // /Users/fintan/workspace/clops/src/Test.g:122:16: ( ' ' | '\\n' | '\\r' | '\\t' )+
            {
            // /Users/fintan/workspace/clops/src/Test.g:122:16: ( ' ' | '\\n' | '\\r' | '\\t' )+
            int cnt5=0;
            loop5:
            do {
                int alt5=2;
                int LA5_0 = input.LA(1);

                if ( ((LA5_0>='\t' && LA5_0<='\n')||LA5_0=='\r'||LA5_0==' ') ) {
                    alt5=1;
                }


                switch (alt5) {
            	case 1 :
            	    // /Users/fintan/workspace/clops/src/Test.g:
            	    {
            	    if ( (input.LA(1)>='\t' && input.LA(1)<='\n')||input.LA(1)=='\r'||input.LA(1)==' ' ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;}


            	    }
            	    break;

            	default :
            	    if ( cnt5 >= 1 ) break loop5;
                        EarlyExitException eee =
                            new EarlyExitException(5, input);
                        throw eee;
                }
                cnt5++;
            } while (true);

            _channel=HIDDEN;

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "WHITESPACE"

    public void mTokens() throws RecognitionException {
        // /Users/fintan/workspace/clops/src/Test.g:1:8: ( T__14 | T__15 | T__16 | T__17 | T__18 | T__19 | T__20 | T__21 | T__22 | T__23 | UNCHECKED_CODE_BLOCK | ALPHANUMERIC | COMMENT | WHITESPACE )
        int alt6=14;
        alt6 = dfa6.predict(input);
        switch (alt6) {
            case 1 :
                // /Users/fintan/workspace/clops/src/Test.g:1:10: T__14
                {
                mT__14(); 

                }
                break;
            case 2 :
                // /Users/fintan/workspace/clops/src/Test.g:1:16: T__15
                {
                mT__15(); 

                }
                break;
            case 3 :
                // /Users/fintan/workspace/clops/src/Test.g:1:22: T__16
                {
                mT__16(); 

                }
                break;
            case 4 :
                // /Users/fintan/workspace/clops/src/Test.g:1:28: T__17
                {
                mT__17(); 

                }
                break;
            case 5 :
                // /Users/fintan/workspace/clops/src/Test.g:1:34: T__18
                {
                mT__18(); 

                }
                break;
            case 6 :
                // /Users/fintan/workspace/clops/src/Test.g:1:40: T__19
                {
                mT__19(); 

                }
                break;
            case 7 :
                // /Users/fintan/workspace/clops/src/Test.g:1:46: T__20
                {
                mT__20(); 

                }
                break;
            case 8 :
                // /Users/fintan/workspace/clops/src/Test.g:1:52: T__21
                {
                mT__21(); 

                }
                break;
            case 9 :
                // /Users/fintan/workspace/clops/src/Test.g:1:58: T__22
                {
                mT__22(); 

                }
                break;
            case 10 :
                // /Users/fintan/workspace/clops/src/Test.g:1:64: T__23
                {
                mT__23(); 

                }
                break;
            case 11 :
                // /Users/fintan/workspace/clops/src/Test.g:1:70: UNCHECKED_CODE_BLOCK
                {
                mUNCHECKED_CODE_BLOCK(); 

                }
                break;
            case 12 :
                // /Users/fintan/workspace/clops/src/Test.g:1:91: ALPHANUMERIC
                {
                mALPHANUMERIC(); 

                }
                break;
            case 13 :
                // /Users/fintan/workspace/clops/src/Test.g:1:104: COMMENT
                {
                mCOMMENT(); 

                }
                break;
            case 14 :
                // /Users/fintan/workspace/clops/src/Test.g:1:112: WHITESPACE
                {
                mWHITESPACE(); 

                }
                break;

        }

    }


    protected DFA6 dfa6 = new DFA6(this);
    static final String DFA6_eotS =
        "\2\uffff\4\13\1\22\2\uffff\1\24\13\uffff";
    static final String DFA6_eofS =
        "\25\uffff";
    static final String DFA6_minS =
        "\1\11\1\uffff\1\141\1\156\1\151\1\141\1\57\2\uffff\1\56\13\uffff";
    static final String DFA6_maxS =
        "\1\173\1\uffff\1\141\1\156\1\151\1\141\1\57\2\uffff\1\56\13\uffff";
    static final String DFA6_acceptS =
        "\1\uffff\1\1\5\uffff\1\7\1\10\1\uffff\1\13\1\14\1\16\1\2\1\3\1\4"+
        "\1\5\1\15\1\6\1\12\1\11";
    static final String DFA6_specialS =
        "\25\uffff}>";
    static final String[] DFA6_transitionS = {
            "\2\14\2\uffff\1\14\22\uffff\1\14\14\uffff\1\7\1\11\1\6\12\13"+
            "\1\1\6\uffff\32\13\4\uffff\1\10\1\uffff\5\13\1\4\2\13\1\3\4"+
            "\13\1\5\7\13\1\2\4\13\1\12",
            "",
            "\1\15",
            "\1\16",
            "\1\17",
            "\1\20",
            "\1\21",
            "",
            "",
            "\1\23",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            ""
    };

    static final short[] DFA6_eot = DFA.unpackEncodedString(DFA6_eotS);
    static final short[] DFA6_eof = DFA.unpackEncodedString(DFA6_eofS);
    static final char[] DFA6_min = DFA.unpackEncodedStringToUnsignedChars(DFA6_minS);
    static final char[] DFA6_max = DFA.unpackEncodedStringToUnsignedChars(DFA6_maxS);
    static final short[] DFA6_accept = DFA.unpackEncodedString(DFA6_acceptS);
    static final short[] DFA6_special = DFA.unpackEncodedString(DFA6_specialS);
    static final short[][] DFA6_transition;

    static {
        int numStates = DFA6_transitionS.length;
        DFA6_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA6_transition[i] = DFA.unpackEncodedString(DFA6_transitionS[i]);
        }
    }

    class DFA6 extends DFA {

        public DFA6(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 6;
            this.eot = DFA6_eot;
            this.eof = DFA6_eof;
            this.min = DFA6_min;
            this.max = DFA6_max;
            this.accept = DFA6_accept;
            this.special = DFA6_special;
            this.transition = DFA6_transition;
        }
        public String getDescription() {
            return "1:1: Tokens : ( T__14 | T__15 | T__16 | T__17 | T__18 | T__19 | T__20 | T__21 | T__22 | T__23 | UNCHECKED_CODE_BLOCK | ALPHANUMERIC | COMMENT | WHITESPACE );";
        }
    }
 

}