// $ANTLR 3.1.3 Mar 18, 2009 10:09:25 /Users/fintan/workspace/clops/src/CLO.g 2009-07-28 15:56:17

  package ie.ucd.clops.dsl.parser;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

public class CLOLexer extends Lexer {
    public static final int T__29=29;
    public static final int SINGLE_LINE_COMMENT=15;
    public static final int T__28=28;
    public static final int UNCHECKED_CODE_BLOCK=11;
    public static final int EOF=-1;
    public static final int UNCHECKED_CODE=14;
    public static final int SECTION_WHERE=9;
    public static final int NAME=5;
    public static final int ALPHANUMERIC=19;
    public static final int DIGIT=22;
    public static final int T__42=42;
    public static final int INTEGER=23;
    public static final int T__43=43;
    public static final int T__40=40;
    public static final int T__41=41;
    public static final int SECTION_OVERRIDES=12;
    public static final int T__46=46;
    public static final int T__47=47;
    public static final int T__44=44;
    public static final int T__45=45;
    public static final int DASH=21;
    public static final int T__48=48;
    public static final int T__49=49;
    public static final int SECTION_FORMAT=8;
    public static final int WHITESPACE=27;
    public static final int UNDERSCORE=20;
    public static final int SECTION_ARGS=6;
    public static final int STRING_CONSTANT=7;
    public static final int MULTI_LINE_COMMENT=16;
    public static final int SECTION_FLY=10;
    public static final int ALPHA=18;
    public static final int REAL=24;
    public static final int T__30=30;
    public static final int T__31=31;
    public static final int T__32=32;
    public static final int T__33=33;
    public static final int T__34=34;
    public static final int T__35=35;
    public static final int NEWLINE=17;
    public static final int T__36=36;
    public static final int T__37=37;
    public static final int T__38=38;
    public static final int T__39=39;
    public static final int SECTION_VALIDITY=13;
    public static final int SECTION_NAME=4;
    public static final int LOWER=25;
    public static final int UPPER=26;

      boolean curliesInJavaMode = false;


    // delegates
    // delegators

    public CLOLexer() {;} 
    public CLOLexer(CharStream input) {
        this(input, new RecognizerSharedState());
    }
    public CLOLexer(CharStream input, RecognizerSharedState state) {
        super(input,state);

    }
    public String getGrammarFileName() { return "/Users/fintan/workspace/clops/src/CLO.g"; }

    // $ANTLR start "T__28"
    public final void mT__28() throws RecognitionException {
        try {
            int _type = T__28;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:10:7: ( ':' )
            // /Users/fintan/workspace/clops/src/CLO.g:10:9: ':'
            {
            match(':'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__28"

    // $ANTLR start "T__29"
    public final void mT__29() throws RecognitionException {
        try {
            int _type = T__29;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:11:7: ( '{' )
            // /Users/fintan/workspace/clops/src/CLO.g:11:9: '{'
            {
            match('{'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__29"

    // $ANTLR start "T__30"
    public final void mT__30() throws RecognitionException {
        try {
            int _type = T__30;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:12:7: ( ',' )
            // /Users/fintan/workspace/clops/src/CLO.g:12:9: ','
            {
            match(','); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__30"

    // $ANTLR start "T__31"
    public final void mT__31() throws RecognitionException {
        try {
            int _type = T__31;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:13:7: ( '}' )
            // /Users/fintan/workspace/clops/src/CLO.g:13:9: '}'
            {
            match('}'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__31"

    // $ANTLR start "T__32"
    public final void mT__32() throws RecognitionException {
        try {
            int _type = T__32;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:14:7: ( '[' )
            // /Users/fintan/workspace/clops/src/CLO.g:14:9: '['
            {
            match('['); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__32"

    // $ANTLR start "T__33"
    public final void mT__33() throws RecognitionException {
        try {
            int _type = T__33;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:15:7: ( '=' )
            // /Users/fintan/workspace/clops/src/CLO.g:15:9: '='
            {
            match('='); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__33"

    // $ANTLR start "T__34"
    public final void mT__34() throws RecognitionException {
        try {
            int _type = T__34;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:16:7: ( ']' )
            // /Users/fintan/workspace/clops/src/CLO.g:16:9: ']'
            {
            match(']'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__34"

    // $ANTLR start "T__35"
    public final void mT__35() throws RecognitionException {
        try {
            int _type = T__35;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:17:7: ( ';' )
            // /Users/fintan/workspace/clops/src/CLO.g:17:9: ';'
            {
            match(';'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__35"

    // $ANTLR start "T__36"
    public final void mT__36() throws RecognitionException {
        try {
            int _type = T__36;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:18:7: ( '(' )
            // /Users/fintan/workspace/clops/src/CLO.g:18:9: '('
            {
            match('('); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__36"

    // $ANTLR start "T__37"
    public final void mT__37() throws RecognitionException {
        try {
            int _type = T__37;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:19:7: ( ')' )
            // /Users/fintan/workspace/clops/src/CLO.g:19:9: ')'
            {
            match(')'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__37"

    // $ANTLR start "T__38"
    public final void mT__38() throws RecognitionException {
        try {
            int _type = T__38;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:20:7: ( '|' )
            // /Users/fintan/workspace/clops/src/CLO.g:20:9: '|'
            {
            match('|'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__38"

    // $ANTLR start "T__39"
    public final void mT__39() throws RecognitionException {
        try {
            int _type = T__39;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:21:7: ( '*' )
            // /Users/fintan/workspace/clops/src/CLO.g:21:9: '*'
            {
            match('*'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__39"

    // $ANTLR start "T__40"
    public final void mT__40() throws RecognitionException {
        try {
            int _type = T__40;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:22:7: ( '+' )
            // /Users/fintan/workspace/clops/src/CLO.g:22:9: '+'
            {
            match('+'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__40"

    // $ANTLR start "T__41"
    public final void mT__41() throws RecognitionException {
        try {
            int _type = T__41;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:23:7: ( '?' )
            // /Users/fintan/workspace/clops/src/CLO.g:23:9: '?'
            {
            match('?'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__41"

    // $ANTLR start "T__42"
    public final void mT__42() throws RecognitionException {
        try {
            int _type = T__42;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:24:7: ( 'OR' )
            // /Users/fintan/workspace/clops/src/CLO.g:24:9: 'OR'
            {
            match("OR"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__42"

    // $ANTLR start "T__43"
    public final void mT__43() throws RecognitionException {
        try {
            int _type = T__43;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:25:7: ( '->' )
            // /Users/fintan/workspace/clops/src/CLO.g:25:9: '->'
            {
            match("->"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__43"

    // $ANTLR start "T__44"
    public final void mT__44() throws RecognitionException {
        try {
            int _type = T__44;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:26:7: ( ':=' )
            // /Users/fintan/workspace/clops/src/CLO.g:26:9: ':='
            {
            match(":="); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__44"

    // $ANTLR start "T__45"
    public final void mT__45() throws RecognitionException {
        try {
            int _type = T__45;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:27:7: ( 'requires' )
            // /Users/fintan/workspace/clops/src/CLO.g:27:9: 'requires'
            {
            match("requires"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__45"

    // $ANTLR start "T__46"
    public final void mT__46() throws RecognitionException {
        try {
            int _type = T__46;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:28:7: ( '=>' )
            // /Users/fintan/workspace/clops/src/CLO.g:28:9: '=>'
            {
            match("=>"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__46"

    // $ANTLR start "T__47"
    public final void mT__47() throws RecognitionException {
        try {
            int _type = T__47;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:29:7: ( '||' )
            // /Users/fintan/workspace/clops/src/CLO.g:29:9: '||'
            {
            match("||"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__47"

    // $ANTLR start "T__48"
    public final void mT__48() throws RecognitionException {
        try {
            int _type = T__48;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:30:7: ( '&&' )
            // /Users/fintan/workspace/clops/src/CLO.g:30:9: '&&'
            {
            match("&&"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__48"

    // $ANTLR start "T__49"
    public final void mT__49() throws RecognitionException {
        try {
            int _type = T__49;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:31:7: ( 'exclusive' )
            // /Users/fintan/workspace/clops/src/CLO.g:31:9: 'exclusive'
            {
            match("exclusive"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "T__49"

    // $ANTLR start "SECTION_NAME"
    public final void mSECTION_NAME() throws RecognitionException {
        try {
            int _type = SECTION_NAME;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:318:13: ( 'NAME::' )
            // /Users/fintan/workspace/clops/src/CLO.g:318:15: 'NAME::'
            {
            match("NAME::"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "SECTION_NAME"

    // $ANTLR start "SECTION_ARGS"
    public final void mSECTION_ARGS() throws RecognitionException {
        try {
            int _type = SECTION_ARGS;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:319:13: ( 'ARGS::' )
            // /Users/fintan/workspace/clops/src/CLO.g:319:15: 'ARGS::'
            {
            match("ARGS::"); 

            curliesInJavaMode=false;

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "SECTION_ARGS"

    // $ANTLR start "SECTION_FORMAT"
    public final void mSECTION_FORMAT() throws RecognitionException {
        try {
            int _type = SECTION_FORMAT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:320:15: ( 'FORMAT::' )
            // /Users/fintan/workspace/clops/src/CLO.g:320:17: 'FORMAT::'
            {
            match("FORMAT::"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "SECTION_FORMAT"

    // $ANTLR start "SECTION_WHERE"
    public final void mSECTION_WHERE() throws RecognitionException {
        try {
            int _type = SECTION_WHERE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:321:14: ( 'WHERE::' )
            // /Users/fintan/workspace/clops/src/CLO.g:321:16: 'WHERE::'
            {
            match("WHERE::"); 


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "SECTION_WHERE"

    // $ANTLR start "SECTION_FLY"
    public final void mSECTION_FLY() throws RecognitionException {
        try {
            int _type = SECTION_FLY;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:322:12: ( 'FLY::' )
            // /Users/fintan/workspace/clops/src/CLO.g:322:14: 'FLY::'
            {
            match("FLY::"); 

            curliesInJavaMode=true;

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "SECTION_FLY"

    // $ANTLR start "SECTION_OVERRIDES"
    public final void mSECTION_OVERRIDES() throws RecognitionException {
        try {
            int _type = SECTION_OVERRIDES;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:323:18: ( 'OVERRIDES::' )
            // /Users/fintan/workspace/clops/src/CLO.g:323:20: 'OVERRIDES::'
            {
            match("OVERRIDES::"); 

            curliesInJavaMode=true;

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "SECTION_OVERRIDES"

    // $ANTLR start "SECTION_VALIDITY"
    public final void mSECTION_VALIDITY() throws RecognitionException {
        try {
            int _type = SECTION_VALIDITY;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:324:17: ( 'VALIDITY::' )
            // /Users/fintan/workspace/clops/src/CLO.g:324:19: 'VALIDITY::'
            {
            match("VALIDITY::"); 

            curliesInJavaMode=true;

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "SECTION_VALIDITY"

    // $ANTLR start "UNCHECKED_CODE_BLOCK"
    public final void mUNCHECKED_CODE_BLOCK() throws RecognitionException {
        try {
            int _type = UNCHECKED_CODE_BLOCK;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:326:23: ({...}? => UNCHECKED_CODE )
            // /Users/fintan/workspace/clops/src/CLO.g:327:3: {...}? => UNCHECKED_CODE
            {
            if ( !((curliesInJavaMode)) ) {
                throw new FailedPredicateException(input, "UNCHECKED_CODE_BLOCK", "curliesInJavaMode");
            }
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
            // /Users/fintan/workspace/clops/src/CLO.g:332:16: ( '{' ( options {greedy=false; k=2; } : UNCHECKED_CODE | SINGLE_LINE_COMMENT | MULTI_LINE_COMMENT | . )* '}' )
            // /Users/fintan/workspace/clops/src/CLO.g:333:2: '{' ( options {greedy=false; k=2; } : UNCHECKED_CODE | SINGLE_LINE_COMMENT | MULTI_LINE_COMMENT | . )* '}'
            {
            match('{'); 
            // /Users/fintan/workspace/clops/src/CLO.g:334:2: ( options {greedy=false; k=2; } : UNCHECKED_CODE | SINGLE_LINE_COMMENT | MULTI_LINE_COMMENT | . )*
            loop1:
            do {
                int alt1=5;
                alt1 = dfa1.predict(input);
                switch (alt1) {
            	case 1 :
            	    // /Users/fintan/workspace/clops/src/CLO.g:335:4: UNCHECKED_CODE
            	    {
            	    mUNCHECKED_CODE(); 

            	    }
            	    break;
            	case 2 :
            	    // /Users/fintan/workspace/clops/src/CLO.g:336:4: SINGLE_LINE_COMMENT
            	    {
            	    mSINGLE_LINE_COMMENT(); 

            	    }
            	    break;
            	case 3 :
            	    // /Users/fintan/workspace/clops/src/CLO.g:337:4: MULTI_LINE_COMMENT
            	    {
            	    mMULTI_LINE_COMMENT(); 

            	    }
            	    break;
            	case 4 :
            	    // /Users/fintan/workspace/clops/src/CLO.g:338:4: .
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

    // $ANTLR start "STRING_CONSTANT"
    public final void mSTRING_CONSTANT() throws RecognitionException {
        try {
            int _type = STRING_CONSTANT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:344:17: ( '\"' ( . )* '\"' )
            // /Users/fintan/workspace/clops/src/CLO.g:344:19: '\"' ( . )* '\"'
            {
            match('\"'); 
            // /Users/fintan/workspace/clops/src/CLO.g:344:23: ( . )*
            loop2:
            do {
                int alt2=2;
                int LA2_0 = input.LA(1);

                if ( (LA2_0=='\"') ) {
                    alt2=2;
                }
                else if ( ((LA2_0>='\u0000' && LA2_0<='!')||(LA2_0>='#' && LA2_0<='\uFFFF')) ) {
                    alt2=1;
                }


                switch (alt2) {
            	case 1 :
            	    // /Users/fintan/workspace/clops/src/CLO.g:344:23: .
            	    {
            	    matchAny(); 

            	    }
            	    break;

            	default :
            	    break loop2;
                }
            } while (true);

            match('\"'); 
             /* FIXME */ 
                setText(getText().substring(1, getText().length() - 1));
              

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "STRING_CONSTANT"

    // $ANTLR start "MULTI_LINE_COMMENT"
    public final void mMULTI_LINE_COMMENT() throws RecognitionException {
        try {
            int _type = MULTI_LINE_COMMENT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:350:21: ( '/*' ( . )* '*/' )
            // /Users/fintan/workspace/clops/src/CLO.g:350:24: '/*' ( . )* '*/'
            {
            match("/*"); 

            // /Users/fintan/workspace/clops/src/CLO.g:350:29: ( . )*
            loop3:
            do {
                int alt3=2;
                int LA3_0 = input.LA(1);

                if ( (LA3_0=='*') ) {
                    int LA3_1 = input.LA(2);

                    if ( (LA3_1=='/') ) {
                        alt3=2;
                    }
                    else if ( ((LA3_1>='\u0000' && LA3_1<='.')||(LA3_1>='0' && LA3_1<='\uFFFF')) ) {
                        alt3=1;
                    }


                }
                else if ( ((LA3_0>='\u0000' && LA3_0<=')')||(LA3_0>='+' && LA3_0<='\uFFFF')) ) {
                    alt3=1;
                }


                switch (alt3) {
            	case 1 :
            	    // /Users/fintan/workspace/clops/src/CLO.g:350:29: .
            	    {
            	    matchAny(); 

            	    }
            	    break;

            	default :
            	    break loop3;
                }
            } while (true);

            match("*/"); 

             _channel=HIDDEN; 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "MULTI_LINE_COMMENT"

    // $ANTLR start "SINGLE_LINE_COMMENT"
    public final void mSINGLE_LINE_COMMENT() throws RecognitionException {
        try {
            int _type = SINGLE_LINE_COMMENT;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:353:22: ( '//' ( . )* NEWLINE )
            // /Users/fintan/workspace/clops/src/CLO.g:353:25: '//' ( . )* NEWLINE
            {
            match("//"); 

            // /Users/fintan/workspace/clops/src/CLO.g:353:30: ( . )*
            loop4:
            do {
                int alt4=2;
                int LA4_0 = input.LA(1);

                if ( (LA4_0=='\r') ) {
                    alt4=2;
                }
                else if ( (LA4_0=='\n') ) {
                    alt4=2;
                }
                else if ( ((LA4_0>='\u0000' && LA4_0<='\t')||(LA4_0>='\u000B' && LA4_0<='\f')||(LA4_0>='\u000E' && LA4_0<='\uFFFF')) ) {
                    alt4=1;
                }


                switch (alt4) {
            	case 1 :
            	    // /Users/fintan/workspace/clops/src/CLO.g:353:30: .
            	    {
            	    matchAny(); 

            	    }
            	    break;

            	default :
            	    break loop4;
                }
            } while (true);

            mNEWLINE(); 
             _channel=HIDDEN; 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "SINGLE_LINE_COMMENT"

    // $ANTLR start "NEWLINE"
    public final void mNEWLINE() throws RecognitionException {
        try {
            // /Users/fintan/workspace/clops/src/CLO.g:357:10: ( ( '\\r' )? '\\n' )
            // /Users/fintan/workspace/clops/src/CLO.g:357:13: ( '\\r' )? '\\n'
            {
            // /Users/fintan/workspace/clops/src/CLO.g:357:13: ( '\\r' )?
            int alt5=2;
            int LA5_0 = input.LA(1);

            if ( (LA5_0=='\r') ) {
                alt5=1;
            }
            switch (alt5) {
                case 1 :
                    // /Users/fintan/workspace/clops/src/CLO.g:357:13: '\\r'
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

    // $ANTLR start "NAME"
    public final void mNAME() throws RecognitionException {
        try {
            int _type = NAME;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:366:7: ( ALPHA ( ALPHANUMERIC | UNDERSCORE | DASH )* )
            // /Users/fintan/workspace/clops/src/CLO.g:366:9: ALPHA ( ALPHANUMERIC | UNDERSCORE | DASH )*
            {
            mALPHA(); 
            // /Users/fintan/workspace/clops/src/CLO.g:366:15: ( ALPHANUMERIC | UNDERSCORE | DASH )*
            loop6:
            do {
                int alt6=2;
                int LA6_0 = input.LA(1);

                if ( (LA6_0=='-'||(LA6_0>='0' && LA6_0<='9')||(LA6_0>='A' && LA6_0<='Z')||LA6_0=='_'||(LA6_0>='a' && LA6_0<='z')) ) {
                    alt6=1;
                }


                switch (alt6) {
            	case 1 :
            	    // /Users/fintan/workspace/clops/src/CLO.g:
            	    {
            	    if ( input.LA(1)=='-'||(input.LA(1)>='0' && input.LA(1)<='9')||(input.LA(1)>='A' && input.LA(1)<='Z')||input.LA(1)=='_'||(input.LA(1)>='a' && input.LA(1)<='z') ) {
            	        input.consume();

            	    }
            	    else {
            	        MismatchedSetException mse = new MismatchedSetException(null,input);
            	        recover(mse);
            	        throw mse;}


            	    }
            	    break;

            	default :
            	    break loop6;
                }
            } while (true);


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "NAME"

    // $ANTLR start "UNDERSCORE"
    public final void mUNDERSCORE() throws RecognitionException {
        try {
            // /Users/fintan/workspace/clops/src/CLO.g:370:13: ( '_' )
            // /Users/fintan/workspace/clops/src/CLO.g:370:16: '_'
            {
            match('_'); 

            }

        }
        finally {
        }
    }
    // $ANTLR end "UNDERSCORE"

    // $ANTLR start "DASH"
    public final void mDASH() throws RecognitionException {
        try {
            int _type = DASH;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:373:7: ( '-' )
            // /Users/fintan/workspace/clops/src/CLO.g:373:10: '-'
            {
            match('-'); 

            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "DASH"

    // $ANTLR start "ALPHANUMERIC"
    public final void mALPHANUMERIC() throws RecognitionException {
        try {
            // /Users/fintan/workspace/clops/src/CLO.g:377:15: ( ALPHA | DIGIT )
            // /Users/fintan/workspace/clops/src/CLO.g:
            {
            if ( (input.LA(1)>='0' && input.LA(1)<='9')||(input.LA(1)>='A' && input.LA(1)<='Z')||(input.LA(1)>='a' && input.LA(1)<='z') ) {
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
    // $ANTLR end "ALPHANUMERIC"

    // $ANTLR start "INTEGER"
    public final void mINTEGER() throws RecognitionException {
        try {
            int _type = INTEGER;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:380:10: ( ( DIGIT )+ )
            // /Users/fintan/workspace/clops/src/CLO.g:380:13: ( DIGIT )+
            {
            // /Users/fintan/workspace/clops/src/CLO.g:380:13: ( DIGIT )+
            int cnt7=0;
            loop7:
            do {
                int alt7=2;
                int LA7_0 = input.LA(1);

                if ( ((LA7_0>='0' && LA7_0<='9')) ) {
                    alt7=1;
                }


                switch (alt7) {
            	case 1 :
            	    // /Users/fintan/workspace/clops/src/CLO.g:380:14: DIGIT
            	    {
            	    mDIGIT(); 

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

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "INTEGER"

    // $ANTLR start "REAL"
    public final void mREAL() throws RecognitionException {
        try {
            int _type = REAL;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:383:7: ( ( DIGIT )+ '.' ( DIGIT )+ )
            // /Users/fintan/workspace/clops/src/CLO.g:383:10: ( DIGIT )+ '.' ( DIGIT )+
            {
            // /Users/fintan/workspace/clops/src/CLO.g:383:10: ( DIGIT )+
            int cnt8=0;
            loop8:
            do {
                int alt8=2;
                int LA8_0 = input.LA(1);

                if ( ((LA8_0>='0' && LA8_0<='9')) ) {
                    alt8=1;
                }


                switch (alt8) {
            	case 1 :
            	    // /Users/fintan/workspace/clops/src/CLO.g:383:10: DIGIT
            	    {
            	    mDIGIT(); 

            	    }
            	    break;

            	default :
            	    if ( cnt8 >= 1 ) break loop8;
                        EarlyExitException eee =
                            new EarlyExitException(8, input);
                        throw eee;
                }
                cnt8++;
            } while (true);

            match('.'); 
            // /Users/fintan/workspace/clops/src/CLO.g:383:21: ( DIGIT )+
            int cnt9=0;
            loop9:
            do {
                int alt9=2;
                int LA9_0 = input.LA(1);

                if ( ((LA9_0>='0' && LA9_0<='9')) ) {
                    alt9=1;
                }


                switch (alt9) {
            	case 1 :
            	    // /Users/fintan/workspace/clops/src/CLO.g:383:21: DIGIT
            	    {
            	    mDIGIT(); 

            	    }
            	    break;

            	default :
            	    if ( cnt9 >= 1 ) break loop9;
                        EarlyExitException eee =
                            new EarlyExitException(9, input);
                        throw eee;
                }
                cnt9++;
            } while (true);


            }

            state.type = _type;
            state.channel = _channel;
        }
        finally {
        }
    }
    // $ANTLR end "REAL"

    // $ANTLR start "DIGIT"
    public final void mDIGIT() throws RecognitionException {
        try {
            // /Users/fintan/workspace/clops/src/CLO.g:387:8: ( '0' .. '9' )
            // /Users/fintan/workspace/clops/src/CLO.g:387:11: '0' .. '9'
            {
            matchRange('0','9'); 

            }

        }
        finally {
        }
    }
    // $ANTLR end "DIGIT"

    // $ANTLR start "ALPHA"
    public final void mALPHA() throws RecognitionException {
        try {
            // /Users/fintan/workspace/clops/src/CLO.g:391:8: ( LOWER | UPPER )
            // /Users/fintan/workspace/clops/src/CLO.g:
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

    // $ANTLR start "LOWER"
    public final void mLOWER() throws RecognitionException {
        try {
            // /Users/fintan/workspace/clops/src/CLO.g:395:8: ( 'a' .. 'z' )
            // /Users/fintan/workspace/clops/src/CLO.g:395:10: 'a' .. 'z'
            {
            matchRange('a','z'); 

            }

        }
        finally {
        }
    }
    // $ANTLR end "LOWER"

    // $ANTLR start "UPPER"
    public final void mUPPER() throws RecognitionException {
        try {
            // /Users/fintan/workspace/clops/src/CLO.g:399:8: ( 'A' .. 'Z' )
            // /Users/fintan/workspace/clops/src/CLO.g:399:10: 'A' .. 'Z'
            {
            matchRange('A','Z'); 

            }

        }
        finally {
        }
    }
    // $ANTLR end "UPPER"

    // $ANTLR start "WHITESPACE"
    public final void mWHITESPACE() throws RecognitionException {
        try {
            int _type = WHITESPACE;
            int _channel = DEFAULT_TOKEN_CHANNEL;
            // /Users/fintan/workspace/clops/src/CLO.g:406:13: ( ( ' ' | '\\n' | '\\r' | '\\t' )+ )
            // /Users/fintan/workspace/clops/src/CLO.g:406:16: ( ' ' | '\\n' | '\\r' | '\\t' )+
            {
            // /Users/fintan/workspace/clops/src/CLO.g:406:16: ( ' ' | '\\n' | '\\r' | '\\t' )+
            int cnt10=0;
            loop10:
            do {
                int alt10=2;
                int LA10_0 = input.LA(1);

                if ( ((LA10_0>='\t' && LA10_0<='\n')||LA10_0=='\r'||LA10_0==' ') ) {
                    alt10=1;
                }


                switch (alt10) {
            	case 1 :
            	    // /Users/fintan/workspace/clops/src/CLO.g:
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
            	    if ( cnt10 >= 1 ) break loop10;
                        EarlyExitException eee =
                            new EarlyExitException(10, input);
                        throw eee;
                }
                cnt10++;
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
        // /Users/fintan/workspace/clops/src/CLO.g:1:8: ( T__28 | T__29 | T__30 | T__31 | T__32 | T__33 | T__34 | T__35 | T__36 | T__37 | T__38 | T__39 | T__40 | T__41 | T__42 | T__43 | T__44 | T__45 | T__46 | T__47 | T__48 | T__49 | SECTION_NAME | SECTION_ARGS | SECTION_FORMAT | SECTION_WHERE | SECTION_FLY | SECTION_OVERRIDES | SECTION_VALIDITY | UNCHECKED_CODE_BLOCK | STRING_CONSTANT | MULTI_LINE_COMMENT | SINGLE_LINE_COMMENT | NAME | DASH | INTEGER | REAL | WHITESPACE )
        int alt11=38;
        alt11 = dfa11.predict(input);
        switch (alt11) {
            case 1 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:10: T__28
                {
                mT__28(); 

                }
                break;
            case 2 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:16: T__29
                {
                mT__29(); 

                }
                break;
            case 3 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:22: T__30
                {
                mT__30(); 

                }
                break;
            case 4 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:28: T__31
                {
                mT__31(); 

                }
                break;
            case 5 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:34: T__32
                {
                mT__32(); 

                }
                break;
            case 6 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:40: T__33
                {
                mT__33(); 

                }
                break;
            case 7 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:46: T__34
                {
                mT__34(); 

                }
                break;
            case 8 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:52: T__35
                {
                mT__35(); 

                }
                break;
            case 9 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:58: T__36
                {
                mT__36(); 

                }
                break;
            case 10 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:64: T__37
                {
                mT__37(); 

                }
                break;
            case 11 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:70: T__38
                {
                mT__38(); 

                }
                break;
            case 12 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:76: T__39
                {
                mT__39(); 

                }
                break;
            case 13 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:82: T__40
                {
                mT__40(); 

                }
                break;
            case 14 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:88: T__41
                {
                mT__41(); 

                }
                break;
            case 15 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:94: T__42
                {
                mT__42(); 

                }
                break;
            case 16 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:100: T__43
                {
                mT__43(); 

                }
                break;
            case 17 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:106: T__44
                {
                mT__44(); 

                }
                break;
            case 18 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:112: T__45
                {
                mT__45(); 

                }
                break;
            case 19 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:118: T__46
                {
                mT__46(); 

                }
                break;
            case 20 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:124: T__47
                {
                mT__47(); 

                }
                break;
            case 21 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:130: T__48
                {
                mT__48(); 

                }
                break;
            case 22 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:136: T__49
                {
                mT__49(); 

                }
                break;
            case 23 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:142: SECTION_NAME
                {
                mSECTION_NAME(); 

                }
                break;
            case 24 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:155: SECTION_ARGS
                {
                mSECTION_ARGS(); 

                }
                break;
            case 25 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:168: SECTION_FORMAT
                {
                mSECTION_FORMAT(); 

                }
                break;
            case 26 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:183: SECTION_WHERE
                {
                mSECTION_WHERE(); 

                }
                break;
            case 27 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:197: SECTION_FLY
                {
                mSECTION_FLY(); 

                }
                break;
            case 28 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:209: SECTION_OVERRIDES
                {
                mSECTION_OVERRIDES(); 

                }
                break;
            case 29 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:227: SECTION_VALIDITY
                {
                mSECTION_VALIDITY(); 

                }
                break;
            case 30 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:244: UNCHECKED_CODE_BLOCK
                {
                mUNCHECKED_CODE_BLOCK(); 

                }
                break;
            case 31 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:265: STRING_CONSTANT
                {
                mSTRING_CONSTANT(); 

                }
                break;
            case 32 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:281: MULTI_LINE_COMMENT
                {
                mMULTI_LINE_COMMENT(); 

                }
                break;
            case 33 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:300: SINGLE_LINE_COMMENT
                {
                mSINGLE_LINE_COMMENT(); 

                }
                break;
            case 34 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:320: NAME
                {
                mNAME(); 

                }
                break;
            case 35 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:325: DASH
                {
                mDASH(); 

                }
                break;
            case 36 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:330: INTEGER
                {
                mINTEGER(); 

                }
                break;
            case 37 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:338: REAL
                {
                mREAL(); 

                }
                break;
            case 38 :
                // /Users/fintan/workspace/clops/src/CLO.g:1:343: WHITESPACE
                {
                mWHITESPACE(); 

                }
                break;

        }

    }


    protected DFA1 dfa1 = new DFA1(this);
    protected DFA11 dfa11 = new DFA11(this);
    static final String DFA1_eotS =
        "\12\uffff";
    static final String DFA1_eofS =
        "\12\uffff";
    static final String DFA1_minS =
        "\1\0\2\uffff\1\0\6\uffff";
    static final String DFA1_maxS =
        "\1\uffff\2\uffff\1\uffff\6\uffff";
    static final String DFA1_acceptS =
        "\1\uffff\1\5\1\1\1\uffff\1\4\1\2\1\3\3\uffff";
    static final String DFA1_specialS =
        "\1\0\2\uffff\1\1\6\uffff}>";
    static final String[] DFA1_transitionS = {
            "\57\4\1\3\113\4\1\2\1\4\1\1\uff82\4",
            "",
            "",
            "\52\4\1\6\4\4\1\5\uffd0\4",
            "",
            "",
            "",
            "",
            "",
            ""
    };

    static final short[] DFA1_eot = DFA.unpackEncodedString(DFA1_eotS);
    static final short[] DFA1_eof = DFA.unpackEncodedString(DFA1_eofS);
    static final char[] DFA1_min = DFA.unpackEncodedStringToUnsignedChars(DFA1_minS);
    static final char[] DFA1_max = DFA.unpackEncodedStringToUnsignedChars(DFA1_maxS);
    static final short[] DFA1_accept = DFA.unpackEncodedString(DFA1_acceptS);
    static final short[] DFA1_special = DFA.unpackEncodedString(DFA1_specialS);
    static final short[][] DFA1_transition;

    static {
        int numStates = DFA1_transitionS.length;
        DFA1_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA1_transition[i] = DFA.unpackEncodedString(DFA1_transitionS[i]);
        }
    }

    class DFA1 extends DFA {

        public DFA1(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 1;
            this.eot = DFA1_eot;
            this.eof = DFA1_eof;
            this.min = DFA1_min;
            this.max = DFA1_max;
            this.accept = DFA1_accept;
            this.special = DFA1_special;
            this.transition = DFA1_transition;
        }
        public String getDescription() {
            return "()* loopback of 334:2: ( options {greedy=false; k=2; } : UNCHECKED_CODE | SINGLE_LINE_COMMENT | MULTI_LINE_COMMENT | . )*";
        }
        public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
            IntStream input = _input;
        	int _s = s;
            switch ( s ) {
                    case 0 : 
                        int LA1_0 = input.LA(1);

                        s = -1;
                        if ( (LA1_0=='}') ) {s = 1;}

                        else if ( (LA1_0=='{') ) {s = 2;}

                        else if ( (LA1_0=='/') ) {s = 3;}

                        else if ( ((LA1_0>='\u0000' && LA1_0<='.')||(LA1_0>='0' && LA1_0<='z')||LA1_0=='|'||(LA1_0>='~' && LA1_0<='\uFFFF')) ) {s = 4;}

                        if ( s>=0 ) return s;
                        break;
                    case 1 : 
                        int LA1_3 = input.LA(1);

                        s = -1;
                        if ( (LA1_3=='/') ) {s = 5;}

                        else if ( (LA1_3=='*') ) {s = 6;}

                        else if ( ((LA1_3>='\u0000' && LA1_3<=')')||(LA1_3>='+' && LA1_3<='.')||(LA1_3>='0' && LA1_3<='\uFFFF')) ) {s = 4;}

                        if ( s>=0 ) return s;
                        break;
            }
            NoViableAltException nvae =
                new NoViableAltException(getDescription(), 1, _s, input);
            error(nvae);
            throw nvae;
        }
    }
    static final String DFA11_eotS =
        "\1\uffff\1\37\1\40\3\uffff\1\43\4\uffff\1\45\3\uffff\1\33\1\51\1"+
        "\33\1\uffff\6\33\3\uffff\1\64\11\uffff\1\66\1\33\2\uffff\10\33\5"+
        "\uffff\17\33\1\uffff\5\33\2\uffff\7\33\1\uffff\4\33\1\uffff\2\33"+
        "\1\141\3\33\1\uffff\1\145\3\uffff";
    static final String DFA11_eofS =
        "\146\uffff";
    static final String DFA11_minS =
        "\1\11\1\75\1\0\3\uffff\1\76\4\uffff\1\174\3\uffff\1\122\1\76\1\145"+
        "\1\uffff\1\170\1\101\1\122\1\114\1\110\1\101\1\uffff\1\52\1\uffff"+
        "\1\56\11\uffff\1\55\1\105\2\uffff\1\161\1\143\1\115\1\107\1\122"+
        "\1\131\1\105\1\114\5\uffff\1\122\1\165\1\154\1\105\1\123\1\115\1"+
        "\72\1\122\1\111\1\122\1\151\1\165\2\72\1\101\1\uffff\1\105\1\104"+
        "\1\111\1\162\1\163\2\uffff\1\124\1\72\1\111\1\104\1\145\1\151\1"+
        "\72\1\uffff\1\124\1\105\1\163\1\166\1\uffff\1\131\1\123\1\55\1\145"+
        "\2\72\1\uffff\1\55\3\uffff";
    static final String DFA11_maxS =
        "\1\175\1\75\1\uffff\3\uffff\1\76\4\uffff\1\174\3\uffff\1\126\1\76"+
        "\1\145\1\uffff\1\170\1\101\1\122\1\117\1\110\1\101\1\uffff\1\57"+
        "\1\uffff\1\71\11\uffff\1\172\1\105\2\uffff\1\161\1\143\1\115\1\107"+
        "\1\122\1\131\1\105\1\114\5\uffff\1\122\1\165\1\154\1\105\1\123\1"+
        "\115\1\72\1\122\1\111\1\122\1\151\1\165\2\72\1\101\1\uffff\1\105"+
        "\1\104\1\111\1\162\1\163\2\uffff\1\124\1\72\1\111\1\104\1\145\1"+
        "\151\1\72\1\uffff\1\124\1\105\1\163\1\166\1\uffff\1\131\1\123\1"+
        "\172\1\145\2\72\1\uffff\1\172\3\uffff";
    static final String DFA11_acceptS =
        "\3\uffff\1\3\1\4\1\5\1\uffff\1\7\1\10\1\11\1\12\1\uffff\1\14\1\15"+
        "\1\16\3\uffff\1\25\6\uffff\1\37\1\uffff\1\42\1\uffff\1\46\1\21\1"+
        "\1\1\2\1\36\1\23\1\6\1\24\1\13\2\uffff\1\20\1\43\10\uffff\1\40\1"+
        "\41\1\44\1\45\1\17\17\uffff\1\33\5\uffff\1\27\1\30\7\uffff\1\32"+
        "\4\uffff\1\31\6\uffff\1\22\1\uffff\1\35\1\34\1\26";
    static final String DFA11_specialS =
        "\2\uffff\1\0\143\uffff}>";
    static final String[] DFA11_transitionS = {
            "\2\35\2\uffff\1\35\22\uffff\1\35\1\uffff\1\31\3\uffff\1\22\1"+
            "\uffff\1\11\1\12\1\14\1\15\1\3\1\20\1\uffff\1\32\12\34\1\1\1"+
            "\10\1\uffff\1\6\1\uffff\1\16\1\uffff\1\25\4\33\1\26\7\33\1\24"+
            "\1\17\6\33\1\30\1\27\3\33\1\5\1\uffff\1\7\3\uffff\4\33\1\23"+
            "\14\33\1\21\10\33\1\2\1\13\1\4",
            "\1\36",
            "\0\41",
            "",
            "",
            "",
            "\1\42",
            "",
            "",
            "",
            "",
            "\1\44",
            "",
            "",
            "",
            "\1\46\3\uffff\1\47",
            "\1\50",
            "\1\52",
            "",
            "\1\53",
            "\1\54",
            "\1\55",
            "\1\57\2\uffff\1\56",
            "\1\60",
            "\1\61",
            "",
            "\1\62\4\uffff\1\63",
            "",
            "\1\65\1\uffff\12\34",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "",
            "\1\33\2\uffff\12\33\7\uffff\32\33\4\uffff\1\33\1\uffff\32\33",
            "\1\67",
            "",
            "",
            "\1\70",
            "\1\71",
            "\1\72",
            "\1\73",
            "\1\74",
            "\1\75",
            "\1\76",
            "\1\77",
            "",
            "",
            "",
            "",
            "",
            "\1\100",
            "\1\101",
            "\1\102",
            "\1\103",
            "\1\104",
            "\1\105",
            "\1\106",
            "\1\107",
            "\1\110",
            "\1\111",
            "\1\112",
            "\1\113",
            "\1\114",
            "\1\115",
            "\1\116",
            "",
            "\1\117",
            "\1\120",
            "\1\121",
            "\1\122",
            "\1\123",
            "",
            "",
            "\1\124",
            "\1\125",
            "\1\126",
            "\1\127",
            "\1\130",
            "\1\131",
            "\1\132",
            "",
            "\1\133",
            "\1\134",
            "\1\135",
            "\1\136",
            "",
            "\1\137",
            "\1\140",
            "\1\33\2\uffff\12\33\7\uffff\32\33\4\uffff\1\33\1\uffff\32\33",
            "\1\142",
            "\1\143",
            "\1\144",
            "",
            "\1\33\2\uffff\12\33\7\uffff\32\33\4\uffff\1\33\1\uffff\32\33",
            "",
            "",
            ""
    };

    static final short[] DFA11_eot = DFA.unpackEncodedString(DFA11_eotS);
    static final short[] DFA11_eof = DFA.unpackEncodedString(DFA11_eofS);
    static final char[] DFA11_min = DFA.unpackEncodedStringToUnsignedChars(DFA11_minS);
    static final char[] DFA11_max = DFA.unpackEncodedStringToUnsignedChars(DFA11_maxS);
    static final short[] DFA11_accept = DFA.unpackEncodedString(DFA11_acceptS);
    static final short[] DFA11_special = DFA.unpackEncodedString(DFA11_specialS);
    static final short[][] DFA11_transition;

    static {
        int numStates = DFA11_transitionS.length;
        DFA11_transition = new short[numStates][];
        for (int i=0; i<numStates; i++) {
            DFA11_transition[i] = DFA.unpackEncodedString(DFA11_transitionS[i]);
        }
    }

    class DFA11 extends DFA {

        public DFA11(BaseRecognizer recognizer) {
            this.recognizer = recognizer;
            this.decisionNumber = 11;
            this.eot = DFA11_eot;
            this.eof = DFA11_eof;
            this.min = DFA11_min;
            this.max = DFA11_max;
            this.accept = DFA11_accept;
            this.special = DFA11_special;
            this.transition = DFA11_transition;
        }
        public String getDescription() {
            return "1:1: Tokens : ( T__28 | T__29 | T__30 | T__31 | T__32 | T__33 | T__34 | T__35 | T__36 | T__37 | T__38 | T__39 | T__40 | T__41 | T__42 | T__43 | T__44 | T__45 | T__46 | T__47 | T__48 | T__49 | SECTION_NAME | SECTION_ARGS | SECTION_FORMAT | SECTION_WHERE | SECTION_FLY | SECTION_OVERRIDES | SECTION_VALIDITY | UNCHECKED_CODE_BLOCK | STRING_CONSTANT | MULTI_LINE_COMMENT | SINGLE_LINE_COMMENT | NAME | DASH | INTEGER | REAL | WHITESPACE );";
        }
        public int specialStateTransition(int s, IntStream _input) throws NoViableAltException {
            IntStream input = _input;
        	int _s = s;
            switch ( s ) {
                    case 0 : 
                        int LA11_2 = input.LA(1);

                         
                        int index11_2 = input.index();
                        input.rewind();
                        s = -1;
                        if ( ((LA11_2>='\u0000' && LA11_2<='\uFFFF')) && ((curliesInJavaMode))) {s = 33;}

                        else s = 32;

                         
                        input.seek(index11_2);
                        if ( s>=0 ) return s;
                        break;
            }
            NoViableAltException nvae =
                new NoViableAltException(getDescription(), 11, _s, input);
            error(nvae);
            throw nvae;
        }
    }
 

}