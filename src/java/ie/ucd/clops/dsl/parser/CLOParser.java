// $ANTLR 3.1.3 Mar 18, 2009 10:09:25 /home/rg/workspace/clops/trunk/src/CLO.g 2009-07-29 12:31:50

  package ie.ucd.clops.dsl.parser; 
  
  import ie.ucd.clops.dsl.structs.*;
  import ie.ucd.clops.dsl.structs.ast.*;
  import ie.ucd.clops.dsl.OptionTypeFactory;
  import ie.ucd.clops.dsl.OptionType;
  import ie.ucd.clops.dsl.UnknownOptionTypeException;
  import ie.ucd.clops.dsl.parser.DSLParseException;
  import ie.ucd.clops.util.Pair;
  
  import java.util.LinkedList;
  import java.util.List;


import org.antlr.runtime.*;
import java.util.Stack;
import java.util.List;
import java.util.ArrayList;

public class CLOParser extends AbstractParser {
    public static final String[] tokenNames = new String[] {
        "<invalid>", "<EOR>", "<DOWN>", "<UP>", "SECTION_NAME", "NAME", "SECTION_ARGS", "STRING_CONSTANT", "SECTION_FORMAT", "SECTION_WHERE", "SECTION_FLY", "UNCHECKED_CODE_BLOCK", "SECTION_OVERRIDES", "SECTION_VALIDITY", "UNCHECKED_CODE", "SINGLE_LINE_COMMENT", "MULTI_LINE_COMMENT", "NEWLINE", "ALPHA", "ALPHANUMERIC", "UNDERSCORE", "DASH", "DIGIT", "INTEGER", "REAL", "LOWER", "UPPER", "WHITESPACE", "':'", "'{'", "','", "'}'", "'['", "'='", "']'", "';'", "'('", "')'", "'|'", "'*'", "'+'", "'?'", "'OR'", "'->'", "':='", "'requires'", "'=>'", "'||'", "'&&'", "'exclusive'"
    };
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
    public static final int INTEGER=23;
    public static final int T__42=42;
    public static final int T__43=43;
    public static final int T__40=40;
    public static final int T__41=41;
    public static final int T__46=46;
    public static final int SECTION_OVERRIDES=12;
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

    // delegates
    // delegators


        public CLOParser(TokenStream input) {
            this(input, new RecognizerSharedState());
        }
        public CLOParser(TokenStream input, RecognizerSharedState state) {
            super(input, state);
             
        }
        

    public String[] getTokenNames() { return CLOParser.tokenNames; }
    public String getGrammarFileName() { return "/home/rg/workspace/clops/trunk/src/CLO.g"; }


      // Nothing now.



    // $ANTLR start "prog"
    // /home/rg/workspace/clops/trunk/src/CLO.g:35:1: prog : clo_specification EOF ;
    public final void prog() throws RecognitionException {
        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:41:7: ( clo_specification EOF )
            // /home/rg/workspace/clops/trunk/src/CLO.g:41:10: clo_specification EOF
            {
            pushFollow(FOLLOW_clo_specification_in_prog58);
            clo_specification();

            state._fsp--;

            match(input,EOF,FOLLOW_EOF_in_prog60); 

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
    // $ANTLR end "prog"


    // $ANTLR start "clo_specification"
    // /home/rg/workspace/clops/trunk/src/CLO.g:44:1: clo_specification : name_section args_section args_format_section ( where_section )? ( fly_section )? ( overrides_section )? ( validity_section )? ;
    public final void clo_specification() throws RecognitionException {
        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:44:20: ( name_section args_section args_format_section ( where_section )? ( fly_section )? ( overrides_section )? ( validity_section )? )
            // /home/rg/workspace/clops/trunk/src/CLO.g:44:23: name_section args_section args_format_section ( where_section )? ( fly_section )? ( overrides_section )? ( validity_section )?
            {
            pushFollow(FOLLOW_name_section_in_clo_specification86);
            name_section();

            state._fsp--;

            pushFollow(FOLLOW_args_section_in_clo_specification110);
            args_section();

            state._fsp--;

            pushFollow(FOLLOW_args_format_section_in_clo_specification134);
            args_format_section();

            state._fsp--;

            // /home/rg/workspace/clops/trunk/src/CLO.g:47:23: ( where_section )?
            int alt1=2;
            int LA1_0 = input.LA(1);

            if ( (LA1_0==SECTION_WHERE) ) {
                alt1=1;
            }
            switch (alt1) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:47:24: where_section
                    {
                    pushFollow(FOLLOW_where_section_in_clo_specification159);
                    where_section();

                    state._fsp--;


                    }
                    break;

            }

            // /home/rg/workspace/clops/trunk/src/CLO.g:48:23: ( fly_section )?
            int alt2=2;
            int LA2_0 = input.LA(1);

            if ( (LA2_0==SECTION_FLY) ) {
                alt2=1;
            }
            switch (alt2) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:48:24: fly_section
                    {
                    pushFollow(FOLLOW_fly_section_in_clo_specification186);
                    fly_section();

                    state._fsp--;


                    }
                    break;

            }

            // /home/rg/workspace/clops/trunk/src/CLO.g:49:23: ( overrides_section )?
            int alt3=2;
            int LA3_0 = input.LA(1);

            if ( (LA3_0==SECTION_OVERRIDES) ) {
                alt3=1;
            }
            switch (alt3) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:49:24: overrides_section
                    {
                    pushFollow(FOLLOW_overrides_section_in_clo_specification213);
                    overrides_section();

                    state._fsp--;


                    }
                    break;

            }

            // /home/rg/workspace/clops/trunk/src/CLO.g:50:23: ( validity_section )?
            int alt4=2;
            int LA4_0 = input.LA(1);

            if ( (LA4_0==SECTION_VALIDITY) ) {
                alt4=1;
            }
            switch (alt4) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:50:24: validity_section
                    {
                    pushFollow(FOLLOW_validity_section_in_clo_specification240);
                    validity_section();

                    state._fsp--;


                    }
                    break;

            }


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
    // $ANTLR end "clo_specification"


    // $ANTLR start "name_section"
    // /home/rg/workspace/clops/trunk/src/CLO.g:53:1: name_section : SECTION_NAME NAME ( ':' s= option_comment )? ;
    public final void name_section() throws RecognitionException {
        Token NAME1=null;
        CLOParser.option_comment_return s = null;


        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:55:15: ( SECTION_NAME NAME ( ':' s= option_comment )? )
            // /home/rg/workspace/clops/trunk/src/CLO.g:55:18: SECTION_NAME NAME ( ':' s= option_comment )?
            {
            match(input,SECTION_NAME,FOLLOW_SECTION_NAME_in_name_section275); 
            NAME1=(Token)match(input,NAME,FOLLOW_NAME_in_name_section277); 
             getDslInformation().setParserName((NAME1!=null?NAME1.getText():null)); 
            // /home/rg/workspace/clops/trunk/src/CLO.g:57:18: ( ':' s= option_comment )?
            int alt5=2;
            int LA5_0 = input.LA(1);

            if ( (LA5_0==28) ) {
                alt5=1;
            }
            switch (alt5) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:57:20: ':' s= option_comment
                    {
                    match(input,28,FOLLOW_28_in_name_section317); 
                    pushFollow(FOLLOW_option_comment_in_name_section321);
                    s=option_comment();

                    state._fsp--;

                     getDslInformation().setParserDescription((s!=null?input.toString(s.start,s.stop):null)); 

                    }
                    break;

            }


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
    // $ANTLR end "name_section"


    // $ANTLR start "args_section"
    // /home/rg/workspace/clops/trunk/src/CLO.g:63:1: args_section : SECTION_ARGS ( arg_definition )+ ;
    public final void args_section() throws RecognitionException {
        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:65:15: ( SECTION_ARGS ( arg_definition )+ )
            // /home/rg/workspace/clops/trunk/src/CLO.g:65:18: SECTION_ARGS ( arg_definition )+
            {
            match(input,SECTION_ARGS,FOLLOW_SECTION_ARGS_in_args_section414); 
            // /home/rg/workspace/clops/trunk/src/CLO.g:65:31: ( arg_definition )+
            int cnt6=0;
            loop6:
            do {
                int alt6=2;
                int LA6_0 = input.LA(1);

                if ( (LA6_0==NAME) ) {
                    alt6=1;
                }


                switch (alt6) {
            	case 1 :
            	    // /home/rg/workspace/clops/trunk/src/CLO.g:65:32: arg_definition
            	    {
            	    pushFollow(FOLLOW_arg_definition_in_args_section417);
            	    arg_definition();

            	    state._fsp--;


            	    }
            	    break;

            	default :
            	    if ( cnt6 >= 1 ) break loop6;
                        EarlyExitException eee =
                            new EarlyExitException(6, input);
                        throw eee;
                }
                cnt6++;
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
    // $ANTLR end "args_section"


    // $ANTLR start "arg_definition"
    // /home/rg/workspace/clops/trunk/src/CLO.g:69:1: arg_definition : id= arg_name ':' '{' (a1= arg_regexp ( ',' a= arg_regexp )* )? '}' ( ( ':' '{' t= NAME '}' ) | ) ( ':' '[' pn1= property_name ( '=' pv1= property_value | ) ( ( ',' )? pn= property_name ( '=' pv= property_value | ) )* ']' )? ( ':' s= option_comment )? ;
    public final void arg_definition() throws RecognitionException {
        Token t=null;
        CLOParser.arg_name_return id = null;

        CLOParser.arg_regexp_return a1 = null;

        CLOParser.arg_regexp_return a = null;

        CLOParser.property_name_return pn1 = null;

        CLOParser.property_value_return pv1 = null;

        CLOParser.property_name_return pn = null;

        CLOParser.property_value_return pv = null;

        CLOParser.option_comment_return s = null;


         BasicOptionDescription option = new BasicOptionDescription(); 
        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:71:17: (id= arg_name ':' '{' (a1= arg_regexp ( ',' a= arg_regexp )* )? '}' ( ( ':' '{' t= NAME '}' ) | ) ( ':' '[' pn1= property_name ( '=' pv1= property_value | ) ( ( ',' )? pn= property_name ( '=' pv= property_value | ) )* ']' )? ( ':' s= option_comment )? )
            // /home/rg/workspace/clops/trunk/src/CLO.g:71:20: id= arg_name ':' '{' (a1= arg_regexp ( ',' a= arg_regexp )* )? '}' ( ( ':' '{' t= NAME '}' ) | ) ( ':' '[' pn1= property_name ( '=' pv1= property_value | ) ( ( ',' )? pn= property_name ( '=' pv= property_value | ) )* ']' )? ( ':' s= option_comment )?
            {
            pushFollow(FOLLOW_arg_name_in_arg_definition469);
            id=arg_name();

            state._fsp--;

             option.setId((id!=null?input.toString(id.start,id.stop):null));
                                 option.setSourceLocation(getSLoc((id!=null?((Token)id.start):null),(id!=null?((Token)id.stop):null))); 
            match(input,28,FOLLOW_28_in_arg_definition512); 
            match(input,29,FOLLOW_29_in_arg_definition514); 
            // /home/rg/workspace/clops/trunk/src/CLO.g:75:20: (a1= arg_regexp ( ',' a= arg_regexp )* )?
            int alt8=2;
            int LA8_0 = input.LA(1);

            if ( (LA8_0==STRING_CONSTANT) ) {
                alt8=1;
            }
            switch (alt8) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:76:22: a1= arg_regexp ( ',' a= arg_regexp )*
                    {
                    pushFollow(FOLLOW_arg_regexp_in_arg_definition561);
                    a1=arg_regexp();

                    state._fsp--;

                     option.addPrefixRegexp((a1!=null?input.toString(a1.start,a1.stop):null)); 
                    // /home/rg/workspace/clops/trunk/src/CLO.g:78:22: ( ',' a= arg_regexp )*
                    loop7:
                    do {
                        int alt7=2;
                        int LA7_0 = input.LA(1);

                        if ( (LA7_0==30) ) {
                            alt7=1;
                        }


                        switch (alt7) {
                    	case 1 :
                    	    // /home/rg/workspace/clops/trunk/src/CLO.g:78:23: ',' a= arg_regexp
                    	    {
                    	    match(input,30,FOLLOW_30_in_arg_definition609); 
                    	    pushFollow(FOLLOW_arg_regexp_in_arg_definition613);
                    	    a=arg_regexp();

                    	    state._fsp--;

                    	     option.addPrefixRegexp((a!=null?input.toString(a.start,a.stop):null)); 

                    	    }
                    	    break;

                    	default :
                    	    break loop7;
                        }
                    } while (true);


                    }
                    break;

            }

            match(input,31,FOLLOW_31_in_arg_definition705); 
            // /home/rg/workspace/clops/trunk/src/CLO.g:83:20: ( ( ':' '{' t= NAME '}' ) | )
            int alt9=2;
            int LA9_0 = input.LA(1);

            if ( (LA9_0==28) ) {
                int LA9_1 = input.LA(2);

                if ( (LA9_1==29) ) {
                    alt9=1;
                }
                else if ( (LA9_1==STRING_CONSTANT||LA9_1==32) ) {
                    alt9=2;
                }
                else {
                    NoViableAltException nvae =
                        new NoViableAltException("", 9, 1, input);

                    throw nvae;
                }
            }
            else if ( (LA9_0==NAME||LA9_0==SECTION_FORMAT) ) {
                alt9=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 9, 0, input);

                throw nvae;
            }
            switch (alt9) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:84:20: ( ':' '{' t= NAME '}' )
                    {
                    // /home/rg/workspace/clops/trunk/src/CLO.g:84:20: ( ':' '{' t= NAME '}' )
                    // /home/rg/workspace/clops/trunk/src/CLO.g:84:22: ':' '{' t= NAME '}'
                    {
                    match(input,28,FOLLOW_28_in_arg_definition749); 
                    match(input,29,FOLLOW_29_in_arg_definition751); 
                    t=(Token)match(input,NAME,FOLLOW_NAME_in_arg_definition755); 
                    match(input,31,FOLLOW_31_in_arg_definition757); 
                     try { OptionType optionType = getOptionTypeFactory().getOptionType((t!=null?t.getText():null)); option.setType(optionType);
                                                 } catch(UnknownOptionTypeException e) { throw new DSLParseException(e.getMessage()); } 
                                           

                    }


                    }
                    break;
                case 2 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:90:24: 
                    {
                     OptionType optionType = getOptionTypeFactory().getDefaultOptionType(); option.setType(optionType); 

                    }
                    break;

            }

            // /home/rg/workspace/clops/trunk/src/CLO.g:92:20: ( ':' '[' pn1= property_name ( '=' pv1= property_value | ) ( ( ',' )? pn= property_name ( '=' pv= property_value | ) )* ']' )?
            int alt14=2;
            int LA14_0 = input.LA(1);

            if ( (LA14_0==28) ) {
                int LA14_1 = input.LA(2);

                if ( (LA14_1==32) ) {
                    alt14=1;
                }
            }
            switch (alt14) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:92:22: ':' '[' pn1= property_name ( '=' pv1= property_value | ) ( ( ',' )? pn= property_name ( '=' pv= property_value | ) )* ']'
                    {
                    match(input,28,FOLLOW_28_in_arg_definition894); 
                    match(input,32,FOLLOW_32_in_arg_definition896); 
                    pushFollow(FOLLOW_property_name_in_arg_definition921);
                    pn1=property_name();

                    state._fsp--;

                     Pair<String,String> property = null; 
                    // /home/rg/workspace/clops/trunk/src/CLO.g:95:22: ( '=' pv1= property_value | )
                    int alt10=2;
                    int LA10_0 = input.LA(1);

                    if ( (LA10_0==33) ) {
                        alt10=1;
                    }
                    else if ( (LA10_0==NAME||LA10_0==30||LA10_0==34) ) {
                        alt10=2;
                    }
                    else {
                        NoViableAltException nvae =
                            new NoViableAltException("", 10, 0, input);

                        throw nvae;
                    }
                    switch (alt10) {
                        case 1 :
                            // /home/rg/workspace/clops/trunk/src/CLO.g:95:24: '=' pv1= property_value
                            {
                            match(input,33,FOLLOW_33_in_arg_definition971); 
                            pushFollow(FOLLOW_property_value_in_arg_definition975);
                            pv1=property_value();

                            state._fsp--;

                             property = new Pair<String,String>((pn1!=null?input.toString(pn1.start,pn1.stop):null), (pv1!=null?input.toString(pv1.start,pv1.stop):null)); 
                                                     getDslInformation().setPropertyValueLocation(property,getSLoc((pv1!=null?((Token)pv1.start):null),(pv1!=null?((Token)pv1.stop):null))); 

                            }
                            break;
                        case 2 :
                            // /home/rg/workspace/clops/trunk/src/CLO.g:99:24: 
                            {
                             property = new Pair<String,String>((pn1!=null?input.toString(pn1.start,pn1.stop):null), "true"); 
                                                     getDslInformation().setPropertyValueLocation(property,getSLoc((pn1!=null?((Token)pn1.start):null),(pn1!=null?((Token)pn1.stop):null))); 

                            }
                            break;

                    }

                     option.setProperty(property); 
                                           getDslInformation().setPropertyNameLocation(property,getSLoc((pn1!=null?((Token)pn1.start):null),(pn1!=null?((Token)pn1.stop):null))); 
                    // /home/rg/workspace/clops/trunk/src/CLO.g:104:22: ( ( ',' )? pn= property_name ( '=' pv= property_value | ) )*
                    loop13:
                    do {
                        int alt13=2;
                        int LA13_0 = input.LA(1);

                        if ( (LA13_0==NAME||LA13_0==30) ) {
                            alt13=1;
                        }


                        switch (alt13) {
                    	case 1 :
                    	    // /home/rg/workspace/clops/trunk/src/CLO.g:104:24: ( ',' )? pn= property_name ( '=' pv= property_value | )
                    	    {
                    	    // /home/rg/workspace/clops/trunk/src/CLO.g:104:24: ( ',' )?
                    	    int alt11=2;
                    	    int LA11_0 = input.LA(1);

                    	    if ( (LA11_0==30) ) {
                    	        alt11=1;
                    	    }
                    	    switch (alt11) {
                    	        case 1 :
                    	            // /home/rg/workspace/clops/trunk/src/CLO.g:104:24: ','
                    	            {
                    	            match(input,30,FOLLOW_30_in_arg_definition1120); 

                    	            }
                    	            break;

                    	    }

                    	    pushFollow(FOLLOW_property_name_in_arg_definition1125);
                    	    pn=property_name();

                    	    state._fsp--;

                    	    // /home/rg/workspace/clops/trunk/src/CLO.g:105:24: ( '=' pv= property_value | )
                    	    int alt12=2;
                    	    int LA12_0 = input.LA(1);

                    	    if ( (LA12_0==33) ) {
                    	        alt12=1;
                    	    }
                    	    else if ( (LA12_0==NAME||LA12_0==30||LA12_0==34) ) {
                    	        alt12=2;
                    	    }
                    	    else {
                    	        NoViableAltException nvae =
                    	            new NoViableAltException("", 12, 0, input);

                    	        throw nvae;
                    	    }
                    	    switch (alt12) {
                    	        case 1 :
                    	            // /home/rg/workspace/clops/trunk/src/CLO.g:105:26: '=' pv= property_value
                    	            {
                    	            match(input,33,FOLLOW_33_in_arg_definition1153); 
                    	            pushFollow(FOLLOW_property_value_in_arg_definition1157);
                    	            pv=property_value();

                    	            state._fsp--;

                    	             property = new Pair<String,String>((pn!=null?input.toString(pn.start,pn.stop):null), (pv!=null?input.toString(pv.start,pv.stop):null));
                    	                                       getDslInformation().setPropertyValueLocation(property,getSLoc((pv!=null?((Token)pv.start):null),(pv!=null?((Token)pv.stop):null))); 

                    	            }
                    	            break;
                    	        case 2 :
                    	            // /home/rg/workspace/clops/trunk/src/CLO.g:109:26: 
                    	            {
                    	             property = new Pair<String,String>((pn!=null?input.toString(pn.start,pn.stop):null), "true");
                    	                                       getDslInformation().setPropertyValueLocation(property,getSLoc((pn!=null?((Token)pn.start):null),(pn!=null?((Token)pn.stop):null))); 

                    	            }
                    	            break;

                    	    }

                    	     option.setProperty(property); 
                    	                             getDslInformation().setPropertyNameLocation(property,getSLoc((pn!=null?((Token)pn.start):null),(pn!=null?((Token)pn.stop):null))); 

                    	    }
                    	    break;

                    	default :
                    	    break loop13;
                        }
                    } while (true);

                    match(input,34,FOLLOW_34_in_arg_definition1335); 

                    }
                    break;

            }

            // /home/rg/workspace/clops/trunk/src/CLO.g:117:20: ( ':' s= option_comment )?
            int alt15=2;
            int LA15_0 = input.LA(1);

            if ( (LA15_0==28) ) {
                alt15=1;
            }
            switch (alt15) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:117:22: ':' s= option_comment
                    {
                    match(input,28,FOLLOW_28_in_arg_definition1381); 
                    pushFollow(FOLLOW_option_comment_in_arg_definition1385);
                    s=option_comment();

                    state._fsp--;

                     option.setDescription((s!=null?input.toString(s.start,s.stop):null)); 

                    }
                    break;

            }

             getDslInformation().addOptionDescription(option); 

            }

        }
        catch (DSLParseException e) {

                              setCustomErrorMessage(e.toString());
                              throw new RecognitionException();
                            
        }
        catch (RecognitionException re) {

                              reportError(re);
                              recover(input,re);
                            
        }
        finally {
        }
        return ;
    }
    // $ANTLR end "arg_definition"

    public static class arg_name_return extends ParserRuleReturnScope {
    };

    // $ANTLR start "arg_name"
    // /home/rg/workspace/clops/trunk/src/CLO.g:133:1: arg_name : NAME ;
    public final CLOParser.arg_name_return arg_name() throws RecognitionException {
        CLOParser.arg_name_return retval = new CLOParser.arg_name_return();
        retval.start = input.LT(1);

        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:133:11: ( NAME )
            // /home/rg/workspace/clops/trunk/src/CLO.g:133:14: NAME
            {
            match(input,NAME,FOLLOW_NAME_in_arg_name1565); 

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
    // $ANTLR end "arg_name"

    public static class arg_regexp_return extends ParserRuleReturnScope {
    };

    // $ANTLR start "arg_regexp"
    // /home/rg/workspace/clops/trunk/src/CLO.g:136:1: arg_regexp : STRING_CONSTANT ;
    public final CLOParser.arg_regexp_return arg_regexp() throws RecognitionException {
        CLOParser.arg_regexp_return retval = new CLOParser.arg_regexp_return();
        retval.start = input.LT(1);

        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:136:13: ( STRING_CONSTANT )
            // /home/rg/workspace/clops/trunk/src/CLO.g:136:16: STRING_CONSTANT
            {
            match(input,STRING_CONSTANT,FOLLOW_STRING_CONSTANT_in_arg_regexp1586); 

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
    // $ANTLR end "arg_regexp"

    public static class property_name_return extends ParserRuleReturnScope {
    };

    // $ANTLR start "property_name"
    // /home/rg/workspace/clops/trunk/src/CLO.g:139:1: property_name : NAME ;
    public final CLOParser.property_name_return property_name() throws RecognitionException {
        CLOParser.property_name_return retval = new CLOParser.property_name_return();
        retval.start = input.LT(1);

        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:139:16: ( NAME )
            // /home/rg/workspace/clops/trunk/src/CLO.g:139:19: NAME
            {
            match(input,NAME,FOLLOW_NAME_in_property_name1620); 

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
    // $ANTLR end "property_name"

    public static class property_value_return extends ParserRuleReturnScope {
    };

    // $ANTLR start "property_value"
    // /home/rg/workspace/clops/trunk/src/CLO.g:142:1: property_value : STRING_CONSTANT ;
    public final CLOParser.property_value_return property_value() throws RecognitionException {
        CLOParser.property_value_return retval = new CLOParser.property_value_return();
        retval.start = input.LT(1);

        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:142:17: ( STRING_CONSTANT )
            // /home/rg/workspace/clops/trunk/src/CLO.g:142:20: STRING_CONSTANT
            {
            match(input,STRING_CONSTANT,FOLLOW_STRING_CONSTANT_in_property_value1661); 

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
    // $ANTLR end "property_value"

    public static class option_comment_return extends ParserRuleReturnScope {
    };

    // $ANTLR start "option_comment"
    // /home/rg/workspace/clops/trunk/src/CLO.g:145:1: option_comment : STRING_CONSTANT ;
    public final CLOParser.option_comment_return option_comment() throws RecognitionException {
        CLOParser.option_comment_return retval = new CLOParser.option_comment_return();
        retval.start = input.LT(1);

        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:145:17: ( STRING_CONSTANT )
            // /home/rg/workspace/clops/trunk/src/CLO.g:145:20: STRING_CONSTANT
            {
            match(input,STRING_CONSTANT,FOLLOW_STRING_CONSTANT_in_option_comment1704); 

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
    // $ANTLR end "option_comment"


    // $ANTLR start "args_format_section"
    // /home/rg/workspace/clops/trunk/src/CLO.g:148:1: args_format_section : SECTION_FORMAT format_clause ( ':' s= option_comment )? ';' ;
    public final void args_format_section() throws RecognitionException {
        CLOParser.option_comment_return s = null;

        CLOParser.format_clause_return format_clause2 = null;


        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:150:22: ( SECTION_FORMAT format_clause ( ':' s= option_comment )? ';' )
            // /home/rg/workspace/clops/trunk/src/CLO.g:150:25: SECTION_FORMAT format_clause ( ':' s= option_comment )? ';'
            {
            match(input,SECTION_FORMAT,FOLLOW_SECTION_FORMAT_in_args_format_section1734); 
            pushFollow(FOLLOW_format_clause_in_args_format_section1736);
            format_clause2=format_clause();

            state._fsp--;

             getDslInformation().setFormatString((format_clause2!=null?input.toString(format_clause2.start,format_clause2.stop):null)); 
                                      getDslInformation().setFormatSourceLocation(getSLoc((format_clause2!=null?((Token)format_clause2.start):null),(format_clause2!=null?((Token)format_clause2.stop):null))); 
            // /home/rg/workspace/clops/trunk/src/CLO.g:153:25: ( ':' s= option_comment )?
            int alt16=2;
            int LA16_0 = input.LA(1);

            if ( (LA16_0==28) ) {
                alt16=1;
            }
            switch (alt16) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:153:26: ':' s= option_comment
                    {
                    match(input,28,FOLLOW_28_in_args_format_section1809); 
                    pushFollow(FOLLOW_option_comment_in_args_format_section1813);
                    s=option_comment();

                    state._fsp--;

                     getDslInformation().setFormatDescription((s!=null?input.toString(s.start,s.stop):null)); 

                    }
                    break;

            }

            match(input,35,FOLLOW_35_in_args_format_section1896); 

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
    // $ANTLR end "args_format_section"

    public static class format_clause_return extends ParserRuleReturnScope {
    };

    // $ANTLR start "format_clause"
    // /home/rg/workspace/clops/trunk/src/CLO.g:159:1: format_clause : format_subclause ;
    public final CLOParser.format_clause_return format_clause() throws RecognitionException {
        CLOParser.format_clause_return retval = new CLOParser.format_clause_return();
        retval.start = input.LT(1);

        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:159:16: ( format_subclause )
            // /home/rg/workspace/clops/trunk/src/CLO.g:159:19: format_subclause
            {
            pushFollow(FOLLOW_format_subclause_in_format_clause1928);
            format_subclause();

            state._fsp--;


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
    // $ANTLR end "format_clause"


    // $ANTLR start "format_subclause"
    // /home/rg/workspace/clops/trunk/src/CLO.g:162:1: format_subclause : ( NAME | ( '(' format_subclause ')' ) ) ( repetition_operator )? ( or_format_subclause )? ;
    public final void format_subclause() throws RecognitionException {
        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:162:19: ( ( NAME | ( '(' format_subclause ')' ) ) ( repetition_operator )? ( or_format_subclause )? )
            // /home/rg/workspace/clops/trunk/src/CLO.g:162:22: ( NAME | ( '(' format_subclause ')' ) ) ( repetition_operator )? ( or_format_subclause )?
            {
            // /home/rg/workspace/clops/trunk/src/CLO.g:162:22: ( NAME | ( '(' format_subclause ')' ) )
            int alt17=2;
            int LA17_0 = input.LA(1);

            if ( (LA17_0==NAME) ) {
                alt17=1;
            }
            else if ( (LA17_0==36) ) {
                alt17=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 17, 0, input);

                throw nvae;
            }
            switch (alt17) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:162:26: NAME
                    {
                    match(input,NAME,FOLLOW_NAME_in_format_subclause1958); 

                    }
                    break;
                case 2 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:163:26: ( '(' format_subclause ')' )
                    {
                    // /home/rg/workspace/clops/trunk/src/CLO.g:163:26: ( '(' format_subclause ')' )
                    // /home/rg/workspace/clops/trunk/src/CLO.g:163:28: '(' format_subclause ')'
                    {
                    match(input,36,FOLLOW_36_in_format_subclause1989); 
                    pushFollow(FOLLOW_format_subclause_in_format_subclause1991);
                    format_subclause();

                    state._fsp--;

                    match(input,37,FOLLOW_37_in_format_subclause1993); 

                    }


                    }
                    break;

            }

            // /home/rg/workspace/clops/trunk/src/CLO.g:165:22: ( repetition_operator )?
            int alt18=2;
            int LA18_0 = input.LA(1);

            if ( ((LA18_0>=39 && LA18_0<=41)) ) {
                alt18=1;
            }
            switch (alt18) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:165:23: repetition_operator
                    {
                    pushFollow(FOLLOW_repetition_operator_in_format_subclause2043);
                    repetition_operator();

                    state._fsp--;


                    }
                    break;

            }

            // /home/rg/workspace/clops/trunk/src/CLO.g:166:22: ( or_format_subclause )?
            int alt19=2;
            int LA19_0 = input.LA(1);

            if ( (LA19_0==NAME||LA19_0==36||LA19_0==38) ) {
                alt19=1;
            }
            switch (alt19) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:166:23: or_format_subclause
                    {
                    pushFollow(FOLLOW_or_format_subclause_in_format_subclause2069);
                    or_format_subclause();

                    state._fsp--;


                    }
                    break;

            }


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
    // $ANTLR end "format_subclause"


    // $ANTLR start "or_format_subclause"
    // /home/rg/workspace/clops/trunk/src/CLO.g:169:1: or_format_subclause : ( '|' )? format_subclause ;
    public final void or_format_subclause() throws RecognitionException {
        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:169:22: ( ( '|' )? format_subclause )
            // /home/rg/workspace/clops/trunk/src/CLO.g:169:25: ( '|' )? format_subclause
            {
            // /home/rg/workspace/clops/trunk/src/CLO.g:169:25: ( '|' )?
            int alt20=2;
            int LA20_0 = input.LA(1);

            if ( (LA20_0==38) ) {
                alt20=1;
            }
            switch (alt20) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:169:26: '|'
                    {
                    match(input,38,FOLLOW_38_in_or_format_subclause2101); 

                    }
                    break;

            }

            pushFollow(FOLLOW_format_subclause_in_or_format_subclause2105);
            format_subclause();

            state._fsp--;


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
    // $ANTLR end "or_format_subclause"


    // $ANTLR start "repetition_operator"
    // /home/rg/workspace/clops/trunk/src/CLO.g:172:1: repetition_operator : ( '*' | '+' | '?' );
    public final void repetition_operator() throws RecognitionException {
        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:172:22: ( '*' | '+' | '?' )
            // /home/rg/workspace/clops/trunk/src/CLO.g:
            {
            if ( (input.LA(1)>=39 && input.LA(1)<=41) ) {
                input.consume();
                state.errorRecovery=false;
            }
            else {
                MismatchedSetException mse = new MismatchedSetException(null,input);
                throw mse;
            }


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
    // $ANTLR end "repetition_operator"


    // $ANTLR start "where_section"
    // /home/rg/workspace/clops/trunk/src/CLO.g:176:1: where_section : SECTION_WHERE ( where_clause )* ;
    public final void where_section() throws RecognitionException {
        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:178:16: ( SECTION_WHERE ( where_clause )* )
            // /home/rg/workspace/clops/trunk/src/CLO.g:178:19: SECTION_WHERE ( where_clause )*
            {
            match(input,SECTION_WHERE,FOLLOW_SECTION_WHERE_in_where_section2179); 
            // /home/rg/workspace/clops/trunk/src/CLO.g:178:33: ( where_clause )*
            loop21:
            do {
                int alt21=2;
                int LA21_0 = input.LA(1);

                if ( (LA21_0==NAME) ) {
                    alt21=1;
                }


                switch (alt21) {
            	case 1 :
            	    // /home/rg/workspace/clops/trunk/src/CLO.g:178:34: where_clause
            	    {
            	    pushFollow(FOLLOW_where_clause_in_where_section2182);
            	    where_clause();

            	    state._fsp--;


            	    }
            	    break;

            	default :
            	    break loop21;
                }
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
    // $ANTLR end "where_section"


    // $ANTLR start "where_clause"
    // /home/rg/workspace/clops/trunk/src/CLO.g:181:1: where_clause returns [WhereClause clause] : group= NAME ':' ( child )+ ';' ;
    public final WhereClause where_clause() throws RecognitionException {
        WhereClause clause = null;

        Token group=null;
        OptionGroupChild child3 = null;


        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:181:43: (group= NAME ':' ( child )+ ';' )
            // /home/rg/workspace/clops/trunk/src/CLO.g:182:3: group= NAME ':' ( child )+ ';'
            {
            group=(Token)match(input,NAME,FOLLOW_NAME_in_where_clause2218); 
             OptionGroupDescription opGroup = new OptionGroupDescription((group!=null?group.getText():null)); 
                opGroup.setSourceLocation(getSLoc(group));
                List<OptionGroupChild> children = new LinkedList<OptionGroupChild>();    
            match(input,28,FOLLOW_28_in_where_clause2227); 
            // /home/rg/workspace/clops/trunk/src/CLO.g:187:3: ( child )+
            int cnt22=0;
            loop22:
            do {
                int alt22=2;
                int LA22_0 = input.LA(1);

                if ( (LA22_0==NAME||LA22_0==DASH||LA22_0==38||LA22_0==40||LA22_0==42) ) {
                    alt22=1;
                }


                switch (alt22) {
            	case 1 :
            	    // /home/rg/workspace/clops/trunk/src/CLO.g:187:5: child
            	    {
            	    pushFollow(FOLLOW_child_in_where_clause2234);
            	    child3=child();

            	    state._fsp--;

            	     opGroup.addChild(child3);
            	          children.add(child3);     

            	    }
            	    break;

            	default :
            	    if ( cnt22 >= 1 ) break loop22;
                        EarlyExitException eee =
                            new EarlyExitException(22, input);
                        throw eee;
                }
                cnt22++;
            } while (true);

             getDslInformation().addOptionGroupDescription(opGroup); 
             clause = WhereClause.mk((group!=null?group.getText():null), children); 
            match(input,35,FOLLOW_35_in_where_clause2263); 

            }

        }
        catch (RecognitionException re) {
            reportError(re);
            recover(input,re);
        }
        finally {
        }
        return clause;
    }
    // $ANTLR end "where_clause"


    // $ANTLR start "child"
    // /home/rg/workspace/clops/trunk/src/CLO.g:197:1: child returns [OptionGroupChild child] : ( ( '-' n= NAME ) | ( ( '+' | 'OR' | '|' )? n= NAME ) );
    public final OptionGroupChild child() throws RecognitionException {
        OptionGroupChild child = null;

        Token n=null;

        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:197:40: ( ( '-' n= NAME ) | ( ( '+' | 'OR' | '|' )? n= NAME ) )
            int alt24=2;
            int LA24_0 = input.LA(1);

            if ( (LA24_0==DASH) ) {
                alt24=1;
            }
            else if ( (LA24_0==NAME||LA24_0==38||LA24_0==40||LA24_0==42) ) {
                alt24=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 24, 0, input);

                throw nvae;
            }
            switch (alt24) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:198:3: ( '-' n= NAME )
                    {
                    // /home/rg/workspace/clops/trunk/src/CLO.g:198:3: ( '-' n= NAME )
                    // /home/rg/workspace/clops/trunk/src/CLO.g:198:5: '-' n= NAME
                    {
                    match(input,DASH,FOLLOW_DASH_in_child2284); 
                    n=(Token)match(input,NAME,FOLLOW_NAME_in_child2288); 
                     child = OptionGroupChild.mk((n!=null?n.getText():null).replaceAll("-", "_"), false, getSLoc(n)); 

                    }


                    }
                    break;
                case 2 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:201:3: ( ( '+' | 'OR' | '|' )? n= NAME )
                    {
                    // /home/rg/workspace/clops/trunk/src/CLO.g:201:3: ( ( '+' | 'OR' | '|' )? n= NAME )
                    // /home/rg/workspace/clops/trunk/src/CLO.g:201:5: ( '+' | 'OR' | '|' )? n= NAME
                    {
                    // /home/rg/workspace/clops/trunk/src/CLO.g:201:5: ( '+' | 'OR' | '|' )?
                    int alt23=2;
                    int LA23_0 = input.LA(1);

                    if ( (LA23_0==38||LA23_0==40||LA23_0==42) ) {
                        alt23=1;
                    }
                    switch (alt23) {
                        case 1 :
                            // /home/rg/workspace/clops/trunk/src/CLO.g:
                            {
                            if ( input.LA(1)==38||input.LA(1)==40||input.LA(1)==42 ) {
                                input.consume();
                                state.errorRecovery=false;
                            }
                            else {
                                MismatchedSetException mse = new MismatchedSetException(null,input);
                                throw mse;
                            }


                            }
                            break;

                    }

                    n=(Token)match(input,NAME,FOLLOW_NAME_in_child2317); 
                     child = OptionGroupChild.mk((n!=null?n.getText():null).replaceAll("-", "_"), true, getSLoc(n)); 

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
        return child;
    }
    // $ANTLR end "child"


    // $ANTLR start "fly_section"
    // /home/rg/workspace/clops/trunk/src/CLO.g:206:1: fly_section : SECTION_FLY ( fly_rule )* ;
    public final void fly_section() throws RecognitionException {
        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:208:14: ( SECTION_FLY ( fly_rule )* )
            // /home/rg/workspace/clops/trunk/src/CLO.g:208:17: SECTION_FLY ( fly_rule )*
            {
            match(input,SECTION_FLY,FOLLOW_SECTION_FLY_in_fly_section2342); 
            // /home/rg/workspace/clops/trunk/src/CLO.g:208:29: ( fly_rule )*
            loop25:
            do {
                int alt25=2;
                int LA25_0 = input.LA(1);

                if ( (LA25_0==NAME) ) {
                    alt25=1;
                }


                switch (alt25) {
            	case 1 :
            	    // /home/rg/workspace/clops/trunk/src/CLO.g:208:30: fly_rule
            	    {
            	    pushFollow(FOLLOW_fly_rule_in_fly_section2345);
            	    fly_rule();

            	    state._fsp--;


            	    }
            	    break;

            	default :
            	    break loop25;
                }
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
    // $ANTLR end "fly_section"


    // $ANTLR start "fly_rule"
    // /home/rg/workspace/clops/trunk/src/CLO.g:211:1: fly_rule : t= NAME ( condition )? '->' n1= NAME ':=' v1= assignment_rhs ( ',' n= NAME ':=' v= assignment_rhs )* ';' ;
    public final void fly_rule() throws RecognitionException {
        Token t=null;
        Token n1=null;
        Token n=null;
        CLOParser.assignment_rhs_return v1 = null;

        CLOParser.assignment_rhs_return v = null;

        CLOParser.condition_return condition4 = null;


        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:211:11: (t= NAME ( condition )? '->' n1= NAME ':=' v1= assignment_rhs ( ',' n= NAME ':=' v= assignment_rhs )* ';' )
            // /home/rg/workspace/clops/trunk/src/CLO.g:211:14: t= NAME ( condition )? '->' n1= NAME ':=' v1= assignment_rhs ( ',' n= NAME ':=' v= assignment_rhs )* ';'
            {
            t=(Token)match(input,NAME,FOLLOW_NAME_in_fly_rule2373); 
             FlyRuleDescription or = new FlyRuleDescription((t!=null?t.getText():null)); 
            // /home/rg/workspace/clops/trunk/src/CLO.g:213:14: ( condition )?
            int alt26=2;
            int LA26_0 = input.LA(1);

            if ( (LA26_0==UNCHECKED_CODE_BLOCK) ) {
                alt26=1;
            }
            switch (alt26) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:214:16: condition
                    {
                    pushFollow(FOLLOW_condition_in_fly_rule2421);
                    condition4=condition();

                    state._fsp--;

                     or.setConditionText((condition4!=null?input.toString(condition4.start,condition4.stop):null)); 

                    }
                    break;

            }

            match(input,43,FOLLOW_43_in_fly_rule2469); 
            n1=(Token)match(input,NAME,FOLLOW_NAME_in_fly_rule2473); 
            match(input,44,FOLLOW_44_in_fly_rule2475); 
            pushFollow(FOLLOW_assignment_rhs_in_fly_rule2479);
            v1=assignment_rhs();

            state._fsp--;

             or.addAssignment(new AssignmentDescription((n1!=null?n1.getText():null), (v1!=null?input.toString(v1.start,v1.stop):null))); 
            // /home/rg/workspace/clops/trunk/src/CLO.g:219:14: ( ',' n= NAME ':=' v= assignment_rhs )*
            loop27:
            do {
                int alt27=2;
                int LA27_0 = input.LA(1);

                if ( (LA27_0==30) ) {
                    alt27=1;
                }


                switch (alt27) {
            	case 1 :
            	    // /home/rg/workspace/clops/trunk/src/CLO.g:219:15: ',' n= NAME ':=' v= assignment_rhs
            	    {
            	    match(input,30,FOLLOW_30_in_fly_rule2511); 
            	    n=(Token)match(input,NAME,FOLLOW_NAME_in_fly_rule2530); 
            	    match(input,44,FOLLOW_44_in_fly_rule2532); 
            	    pushFollow(FOLLOW_assignment_rhs_in_fly_rule2536);
            	    v=assignment_rhs();

            	    state._fsp--;

            	     or.addAssignment(new AssignmentDescription((n!=null?n.getText():null), (v!=null?input.toString(v.start,v.stop):null))); 

            	    }
            	    break;

            	default :
            	    break loop27;
                }
            } while (true);

            match(input,35,FOLLOW_35_in_fly_rule2570); 
             getDslInformation().addFlyRuleDescription(or); 

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
    // $ANTLR end "fly_rule"

    public static class condition_return extends ParserRuleReturnScope {
    };

    // $ANTLR start "condition"
    // /home/rg/workspace/clops/trunk/src/CLO.g:226:1: condition : UNCHECKED_CODE_BLOCK ;
    public final CLOParser.condition_return condition() throws RecognitionException {
        CLOParser.condition_return retval = new CLOParser.condition_return();
        retval.start = input.LT(1);

        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:226:12: ( UNCHECKED_CODE_BLOCK )
            // /home/rg/workspace/clops/trunk/src/CLO.g:226:15: UNCHECKED_CODE_BLOCK
            {
            match(input,UNCHECKED_CODE_BLOCK,FOLLOW_UNCHECKED_CODE_BLOCK_in_condition2616); 

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
    // $ANTLR end "condition"

    public static class assignment_rhs_return extends ParserRuleReturnScope {
    };

    // $ANTLR start "assignment_rhs"
    // /home/rg/workspace/clops/trunk/src/CLO.g:229:1: assignment_rhs : UNCHECKED_CODE_BLOCK ;
    public final CLOParser.assignment_rhs_return assignment_rhs() throws RecognitionException {
        CLOParser.assignment_rhs_return retval = new CLOParser.assignment_rhs_return();
        retval.start = input.LT(1);

        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:229:17: ( UNCHECKED_CODE_BLOCK )
            // /home/rg/workspace/clops/trunk/src/CLO.g:229:20: UNCHECKED_CODE_BLOCK
            {
            match(input,UNCHECKED_CODE_BLOCK,FOLLOW_UNCHECKED_CODE_BLOCK_in_assignment_rhs2648); 

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
    // $ANTLR end "assignment_rhs"


    // $ANTLR start "overrides_section"
    // /home/rg/workspace/clops/trunk/src/CLO.g:233:1: overrides_section : SECTION_OVERRIDES ( override_rule )* ;
    public final void overrides_section() throws RecognitionException {
        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:235:20: ( SECTION_OVERRIDES ( override_rule )* )
            // /home/rg/workspace/clops/trunk/src/CLO.g:235:23: SECTION_OVERRIDES ( override_rule )*
            {
            match(input,SECTION_OVERRIDES,FOLLOW_SECTION_OVERRIDES_in_overrides_section2679); 
            // /home/rg/workspace/clops/trunk/src/CLO.g:235:41: ( override_rule )*
            loop28:
            do {
                int alt28=2;
                int LA28_0 = input.LA(1);

                if ( (LA28_0==UNCHECKED_CODE_BLOCK) ) {
                    alt28=1;
                }


                switch (alt28) {
            	case 1 :
            	    // /home/rg/workspace/clops/trunk/src/CLO.g:235:42: override_rule
            	    {
            	    pushFollow(FOLLOW_override_rule_in_overrides_section2682);
            	    override_rule();

            	    state._fsp--;


            	    }
            	    break;

            	default :
            	    break loop28;
                }
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
    // $ANTLR end "overrides_section"


    // $ANTLR start "override_rule"
    // /home/rg/workspace/clops/trunk/src/CLO.g:238:1: override_rule : condition '->' n1= NAME ':=' v1= assignment_rhs ( ',' n= NAME ':=' v= assignment_rhs )* ';' ;
    public final void override_rule() throws RecognitionException {
        Token n1=null;
        Token n=null;
        CLOParser.assignment_rhs_return v1 = null;

        CLOParser.assignment_rhs_return v = null;

        CLOParser.condition_return condition5 = null;


        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:238:16: ( condition '->' n1= NAME ':=' v1= assignment_rhs ( ',' n= NAME ':=' v= assignment_rhs )* ';' )
            // /home/rg/workspace/clops/trunk/src/CLO.g:238:19: condition '->' n1= NAME ':=' v1= assignment_rhs ( ',' n= NAME ':=' v= assignment_rhs )* ';'
            {
            pushFollow(FOLLOW_condition_in_override_rule2714);
            condition5=condition();

            state._fsp--;

            match(input,43,FOLLOW_43_in_override_rule2716); 
             OverrideRuleDescription ord = new OverrideRuleDescription(); 
                                ord.setConditionText((condition5!=null?input.toString(condition5.start,condition5.stop):null));                            
            n1=(Token)match(input,NAME,FOLLOW_NAME_in_override_rule2760); 
            match(input,44,FOLLOW_44_in_override_rule2762); 
            pushFollow(FOLLOW_assignment_rhs_in_override_rule2766);
            v1=assignment_rhs();

            state._fsp--;

             ord.addAssignment(new AssignmentDescription((n1!=null?n1.getText():null), (v1!=null?input.toString(v1.start,v1.stop):null))); 
            // /home/rg/workspace/clops/trunk/src/CLO.g:243:19: ( ',' n= NAME ':=' v= assignment_rhs )*
            loop29:
            do {
                int alt29=2;
                int LA29_0 = input.LA(1);

                if ( (LA29_0==30) ) {
                    alt29=1;
                }


                switch (alt29) {
            	case 1 :
            	    // /home/rg/workspace/clops/trunk/src/CLO.g:243:20: ',' n= NAME ':=' v= assignment_rhs
            	    {
            	    match(input,30,FOLLOW_30_in_override_rule2808); 
            	    n=(Token)match(input,NAME,FOLLOW_NAME_in_override_rule2833); 
            	    match(input,44,FOLLOW_44_in_override_rule2835); 
            	    pushFollow(FOLLOW_assignment_rhs_in_override_rule2839);
            	    v=assignment_rhs();

            	    state._fsp--;

            	     ord.addAssignment(new AssignmentDescription((n!=null?n.getText():null), (v!=null?input.toString(v.start,v.stop):null))); 

            	    }
            	    break;

            	default :
            	    break loop29;
                }
            } while (true);

             getDslInformation().addOverrideRuleDescription(ord); 
            match(input,35,FOLLOW_35_in_override_rule2923); 

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
    // $ANTLR end "override_rule"


    // $ANTLR start "validity_section"
    // /home/rg/workspace/clops/trunk/src/CLO.g:251:1: validity_section : SECTION_VALIDITY ( validity_rule )* ;
    public final void validity_section() throws RecognitionException {
        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:253:19: ( SECTION_VALIDITY ( validity_rule )* )
            // /home/rg/workspace/clops/trunk/src/CLO.g:253:22: SECTION_VALIDITY ( validity_rule )*
            {
            match(input,SECTION_VALIDITY,FOLLOW_SECTION_VALIDITY_in_validity_section2952); 
            // /home/rg/workspace/clops/trunk/src/CLO.g:253:39: ( validity_rule )*
            loop30:
            do {
                int alt30=2;
                int LA30_0 = input.LA(1);

                if ( (LA30_0==UNCHECKED_CODE_BLOCK||LA30_0==45||LA30_0==49) ) {
                    alt30=1;
                }


                switch (alt30) {
            	case 1 :
            	    // /home/rg/workspace/clops/trunk/src/CLO.g:253:40: validity_rule
            	    {
            	    pushFollow(FOLLOW_validity_rule_in_validity_section2955);
            	    validity_rule();

            	    state._fsp--;


            	    }
            	    break;

            	default :
            	    break loop30;
                }
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
    // $ANTLR end "validity_section"


    // $ANTLR start "validity_rule"
    // /home/rg/workspace/clops/trunk/src/CLO.g:256:1: validity_rule : ( standard_validity_rule | requires_validity_rule | exclusive_validity_rule );
    public final void validity_rule() throws RecognitionException {
        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:256:16: ( standard_validity_rule | requires_validity_rule | exclusive_validity_rule )
            int alt31=3;
            switch ( input.LA(1) ) {
            case UNCHECKED_CODE_BLOCK:
                {
                alt31=1;
                }
                break;
            case 45:
                {
                alt31=2;
                }
                break;
            case 49:
                {
                alt31=3;
                }
                break;
            default:
                NoViableAltException nvae =
                    new NoViableAltException("", 31, 0, input);

                throw nvae;
            }

            switch (alt31) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:256:20: standard_validity_rule
                    {
                    pushFollow(FOLLOW_standard_validity_rule_in_validity_rule2987);
                    standard_validity_rule();

                    state._fsp--;


                    }
                    break;
                case 2 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:257:20: requires_validity_rule
                    {
                    pushFollow(FOLLOW_requires_validity_rule_in_validity_rule3008);
                    requires_validity_rule();

                    state._fsp--;


                    }
                    break;
                case 3 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:258:20: exclusive_validity_rule
                    {
                    pushFollow(FOLLOW_exclusive_validity_rule_in_validity_rule3029);
                    exclusive_validity_rule();

                    state._fsp--;


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
        return ;
    }
    // $ANTLR end "validity_rule"


    // $ANTLR start "standard_validity_rule"
    // /home/rg/workspace/clops/trunk/src/CLO.g:261:1: standard_validity_rule : condition ( ':' explanation )? ';' ;
    public final void standard_validity_rule() throws RecognitionException {
        CLOParser.condition_return condition6 = null;

        CLOParser.explanation_return explanation7 = null;


        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:261:25: ( condition ( ':' explanation )? ';' )
            // /home/rg/workspace/clops/trunk/src/CLO.g:261:28: condition ( ':' explanation )? ';'
            {
            pushFollow(FOLLOW_condition_in_standard_validity_rule3055);
            condition6=condition();

            state._fsp--;

             ValidityRuleDescription vrd = new ValidityRuleDescription(); 
                                         vrd.setConditionText((condition6!=null?input.toString(condition6.start,condition6.stop):null));                            
            // /home/rg/workspace/clops/trunk/src/CLO.g:264:28: ( ':' explanation )?
            int alt32=2;
            int LA32_0 = input.LA(1);

            if ( (LA32_0==28) ) {
                alt32=1;
            }
            switch (alt32) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:264:30: ':' explanation
                    {
                    match(input,28,FOLLOW_28_in_standard_validity_rule3115); 
                    pushFollow(FOLLOW_explanation_in_standard_validity_rule3117);
                    explanation7=explanation();

                    state._fsp--;

                     vrd.setExplanation((explanation7!=null?input.toString(explanation7.start,explanation7.stop):null)); 

                    }
                    break;

            }

             getDslInformation().addValidityRuleDescription(vrd); 
            match(input,35,FOLLOW_35_in_standard_validity_rule3238); 

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
    // $ANTLR end "standard_validity_rule"


    // $ANTLR start "requires_validity_rule"
    // /home/rg/workspace/clops/trunk/src/CLO.g:271:1: requires_validity_rule : 'requires' ':' arg_name '=>' requires_expression ( ':' explanation )? ';' ;
    public final void requires_validity_rule() throws RecognitionException {
        CLOParser.arg_name_return arg_name8 = null;

        CLOParser.requires_expression_return requires_expression9 = null;

        CLOParser.explanation_return explanation10 = null;


        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:271:25: ( 'requires' ':' arg_name '=>' requires_expression ( ':' explanation )? ';' )
            // /home/rg/workspace/clops/trunk/src/CLO.g:271:28: 'requires' ':' arg_name '=>' requires_expression ( ':' explanation )? ';'
            {
            match(input,45,FOLLOW_45_in_requires_validity_rule3273); 
            match(input,28,FOLLOW_28_in_requires_validity_rule3275); 
            pushFollow(FOLLOW_arg_name_in_requires_validity_rule3277);
            arg_name8=arg_name();

            state._fsp--;

            match(input,46,FOLLOW_46_in_requires_validity_rule3279); 
            pushFollow(FOLLOW_requires_expression_in_requires_validity_rule3281);
            requires_expression9=requires_expression();

            state._fsp--;

             ValidityRuleDescription vrd = ValidityRuleDescription.fromRequires((arg_name8!=null?input.toString(arg_name8.start,arg_name8.stop):null), (requires_expression9!=null?input.toString(requires_expression9.start,requires_expression9.stop):null)); 
            // /home/rg/workspace/clops/trunk/src/CLO.g:273:28: ( ':' explanation )?
            int alt33=2;
            int LA33_0 = input.LA(1);

            if ( (LA33_0==28) ) {
                alt33=1;
            }
            switch (alt33) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:273:30: ':' explanation
                    {
                    match(input,28,FOLLOW_28_in_requires_validity_rule3341); 
                    pushFollow(FOLLOW_explanation_in_requires_validity_rule3343);
                    explanation10=explanation();

                    state._fsp--;

                     vrd.setExplanation((explanation10!=null?input.toString(explanation10.start,explanation10.stop):null)); 

                    }
                    break;

            }

             getDslInformation().addValidityRuleDescription(vrd); 
            match(input,35,FOLLOW_35_in_requires_validity_rule3461); 

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
    // $ANTLR end "requires_validity_rule"

    public static class requires_expression_return extends ParserRuleReturnScope {
    };

    // $ANTLR start "requires_expression"
    // /home/rg/workspace/clops/trunk/src/CLO.g:280:1: requires_expression : requires_or_expression ;
    public final CLOParser.requires_expression_return requires_expression() throws RecognitionException {
        CLOParser.requires_expression_return retval = new CLOParser.requires_expression_return();
        retval.start = input.LT(1);

        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:280:22: ( requires_or_expression )
            // /home/rg/workspace/clops/trunk/src/CLO.g:280:26: requires_or_expression
            {
            pushFollow(FOLLOW_requires_or_expression_in_requires_expression3497);
            requires_or_expression();

            state._fsp--;


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
    // $ANTLR end "requires_expression"


    // $ANTLR start "requires_or_expression"
    // /home/rg/workspace/clops/trunk/src/CLO.g:283:1: requires_or_expression : requires_and_expression ( '||' requires_and_expression )* ;
    public final void requires_or_expression() throws RecognitionException {
        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:283:25: ( requires_and_expression ( '||' requires_and_expression )* )
            // /home/rg/workspace/clops/trunk/src/CLO.g:283:28: requires_and_expression ( '||' requires_and_expression )*
            {
            pushFollow(FOLLOW_requires_and_expression_in_requires_or_expression3550);
            requires_and_expression();

            state._fsp--;

            // /home/rg/workspace/clops/trunk/src/CLO.g:283:52: ( '||' requires_and_expression )*
            loop34:
            do {
                int alt34=2;
                int LA34_0 = input.LA(1);

                if ( (LA34_0==47) ) {
                    alt34=1;
                }


                switch (alt34) {
            	case 1 :
            	    // /home/rg/workspace/clops/trunk/src/CLO.g:283:54: '||' requires_and_expression
            	    {
            	    match(input,47,FOLLOW_47_in_requires_or_expression3554); 
            	    pushFollow(FOLLOW_requires_and_expression_in_requires_or_expression3556);
            	    requires_and_expression();

            	    state._fsp--;


            	    }
            	    break;

            	default :
            	    break loop34;
                }
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
    // $ANTLR end "requires_or_expression"


    // $ANTLR start "requires_and_expression"
    // /home/rg/workspace/clops/trunk/src/CLO.g:286:1: requires_and_expression : requires_expression_unit ( '&&' requires_expression_unit )* ;
    public final void requires_and_expression() throws RecognitionException {
        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:286:26: ( requires_expression_unit ( '&&' requires_expression_unit )* )
            // /home/rg/workspace/clops/trunk/src/CLO.g:286:29: requires_expression_unit ( '&&' requires_expression_unit )*
            {
            pushFollow(FOLLOW_requires_expression_unit_in_requires_and_expression3618);
            requires_expression_unit();

            state._fsp--;

            // /home/rg/workspace/clops/trunk/src/CLO.g:286:54: ( '&&' requires_expression_unit )*
            loop35:
            do {
                int alt35=2;
                int LA35_0 = input.LA(1);

                if ( (LA35_0==48) ) {
                    alt35=1;
                }


                switch (alt35) {
            	case 1 :
            	    // /home/rg/workspace/clops/trunk/src/CLO.g:286:56: '&&' requires_expression_unit
            	    {
            	    match(input,48,FOLLOW_48_in_requires_and_expression3622); 
            	    pushFollow(FOLLOW_requires_expression_unit_in_requires_and_expression3624);
            	    requires_expression_unit();

            	    state._fsp--;


            	    }
            	    break;

            	default :
            	    break loop35;
                }
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
    // $ANTLR end "requires_and_expression"


    // $ANTLR start "requires_expression_unit"
    // /home/rg/workspace/clops/trunk/src/CLO.g:289:1: requires_expression_unit : ( arg_name | ( '(' requires_expression ')' ) );
    public final void requires_expression_unit() throws RecognitionException {
        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:289:27: ( arg_name | ( '(' requires_expression ')' ) )
            int alt36=2;
            int LA36_0 = input.LA(1);

            if ( (LA36_0==NAME) ) {
                alt36=1;
            }
            else if ( (LA36_0==36) ) {
                alt36=2;
            }
            else {
                NoViableAltException nvae =
                    new NoViableAltException("", 36, 0, input);

                throw nvae;
            }
            switch (alt36) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:289:32: arg_name
                    {
                    pushFollow(FOLLOW_arg_name_in_requires_expression_unit3690);
                    arg_name();

                    state._fsp--;


                    }
                    break;
                case 2 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:290:32: ( '(' requires_expression ')' )
                    {
                    // /home/rg/workspace/clops/trunk/src/CLO.g:290:32: ( '(' requires_expression ')' )
                    // /home/rg/workspace/clops/trunk/src/CLO.g:290:34: '(' requires_expression ')'
                    {
                    match(input,36,FOLLOW_36_in_requires_expression_unit3726); 
                    pushFollow(FOLLOW_requires_expression_in_requires_expression_unit3728);
                    requires_expression();

                    state._fsp--;

                    match(input,37,FOLLOW_37_in_requires_expression_unit3730); 

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
        return ;
    }
    // $ANTLR end "requires_expression_unit"


    // $ANTLR start "exclusive_validity_rule"
    // /home/rg/workspace/clops/trunk/src/CLO.g:294:1: exclusive_validity_rule : 'exclusive' ':' a1= arg_name ( ',' a= arg_name )+ ( ':' explanation )? ';' ;
    public final void exclusive_validity_rule() throws RecognitionException {
        CLOParser.arg_name_return a1 = null;

        CLOParser.arg_name_return a = null;

        CLOParser.explanation_return explanation11 = null;


        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:294:26: ( 'exclusive' ':' a1= arg_name ( ',' a= arg_name )+ ( ':' explanation )? ';' )
            // /home/rg/workspace/clops/trunk/src/CLO.g:294:29: 'exclusive' ':' a1= arg_name ( ',' a= arg_name )+ ( ':' explanation )? ';'
            {
            match(input,49,FOLLOW_49_in_exclusive_validity_rule3791); 
            match(input,28,FOLLOW_28_in_exclusive_validity_rule3793); 
            pushFollow(FOLLOW_arg_name_in_exclusive_validity_rule3797);
            a1=arg_name();

            state._fsp--;

             List<String> args = new java.util.LinkedList<String>();
                                             args.add((a1!=null?input.toString(a1.start,a1.stop):null));                                    
            // /home/rg/workspace/clops/trunk/src/CLO.g:297:32: ( ',' a= arg_name )+
            int cnt37=0;
            loop37:
            do {
                int alt37=2;
                int LA37_0 = input.LA(1);

                if ( (LA37_0==30) ) {
                    alt37=1;
                }


                switch (alt37) {
            	case 1 :
            	    // /home/rg/workspace/clops/trunk/src/CLO.g:297:34: ',' a= arg_name
            	    {
            	    match(input,30,FOLLOW_30_in_exclusive_validity_rule3865); 
            	    pushFollow(FOLLOW_arg_name_in_exclusive_validity_rule3869);
            	    a=arg_name();

            	    state._fsp--;

            	     args.add((a!=null?input.toString(a.start,a.stop):null)); 

            	    }
            	    break;

            	default :
            	    if ( cnt37 >= 1 ) break loop37;
                        EarlyExitException eee =
                            new EarlyExitException(37, input);
                        throw eee;
                }
                cnt37++;
            } while (true);

             ValidityRuleDescription vrd = ValidityRuleDescription.fromXOR(args); 
            // /home/rg/workspace/clops/trunk/src/CLO.g:301:32: ( ':' explanation )?
            int alt38=2;
            int LA38_0 = input.LA(1);

            if ( (LA38_0==28) ) {
                alt38=1;
            }
            switch (alt38) {
                case 1 :
                    // /home/rg/workspace/clops/trunk/src/CLO.g:302:33: ':' explanation
                    {
                    match(input,28,FOLLOW_28_in_exclusive_validity_rule4039); 
                    pushFollow(FOLLOW_explanation_in_exclusive_validity_rule4041);
                    explanation11=explanation();

                    state._fsp--;

                     vrd.setExplanation((explanation11!=null?input.toString(explanation11.start,explanation11.stop):null)); 

                    }
                    break;

            }

             getDslInformation().addValidityRuleDescription(vrd); 
            match(input,35,FOLLOW_35_in_exclusive_validity_rule4176); 

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
    // $ANTLR end "exclusive_validity_rule"

    public static class explanation_return extends ParserRuleReturnScope {
    };

    // $ANTLR start "explanation"
    // /home/rg/workspace/clops/trunk/src/CLO.g:309:1: explanation : STRING_CONSTANT ;
    public final CLOParser.explanation_return explanation() throws RecognitionException {
        CLOParser.explanation_return retval = new CLOParser.explanation_return();
        retval.start = input.LT(1);

        try {
            // /home/rg/workspace/clops/trunk/src/CLO.g:309:14: ( STRING_CONSTANT )
            // /home/rg/workspace/clops/trunk/src/CLO.g:309:17: STRING_CONSTANT
            {
            match(input,STRING_CONSTANT,FOLLOW_STRING_CONSTANT_in_explanation4230); 

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
    // $ANTLR end "explanation"

    // Delegated rules


 

    public static final BitSet FOLLOW_clo_specification_in_prog58 = new BitSet(new long[]{0x0000000000000000L});
    public static final BitSet FOLLOW_EOF_in_prog60 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_name_section_in_clo_specification86 = new BitSet(new long[]{0x0000000000000040L});
    public static final BitSet FOLLOW_args_section_in_clo_specification110 = new BitSet(new long[]{0x0000000000000100L});
    public static final BitSet FOLLOW_args_format_section_in_clo_specification134 = new BitSet(new long[]{0x0000000000003602L});
    public static final BitSet FOLLOW_where_section_in_clo_specification159 = new BitSet(new long[]{0x0000000000003402L});
    public static final BitSet FOLLOW_fly_section_in_clo_specification186 = new BitSet(new long[]{0x0000000000003002L});
    public static final BitSet FOLLOW_overrides_section_in_clo_specification213 = new BitSet(new long[]{0x0000000000002002L});
    public static final BitSet FOLLOW_validity_section_in_clo_specification240 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SECTION_NAME_in_name_section275 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_NAME_in_name_section277 = new BitSet(new long[]{0x0000000010000002L});
    public static final BitSet FOLLOW_28_in_name_section317 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_option_comment_in_name_section321 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SECTION_ARGS_in_args_section414 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_arg_definition_in_args_section417 = new BitSet(new long[]{0x0000000000000022L});
    public static final BitSet FOLLOW_arg_name_in_arg_definition469 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_28_in_arg_definition512 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_29_in_arg_definition514 = new BitSet(new long[]{0x0000000080000080L});
    public static final BitSet FOLLOW_arg_regexp_in_arg_definition561 = new BitSet(new long[]{0x00000000C0000000L});
    public static final BitSet FOLLOW_30_in_arg_definition609 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_arg_regexp_in_arg_definition613 = new BitSet(new long[]{0x00000000C0000000L});
    public static final BitSet FOLLOW_31_in_arg_definition705 = new BitSet(new long[]{0x0000000010000002L});
    public static final BitSet FOLLOW_28_in_arg_definition749 = new BitSet(new long[]{0x0000000020000000L});
    public static final BitSet FOLLOW_29_in_arg_definition751 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_NAME_in_arg_definition755 = new BitSet(new long[]{0x0000000080000000L});
    public static final BitSet FOLLOW_31_in_arg_definition757 = new BitSet(new long[]{0x0000000010000002L});
    public static final BitSet FOLLOW_28_in_arg_definition894 = new BitSet(new long[]{0x0000000100000000L});
    public static final BitSet FOLLOW_32_in_arg_definition896 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_property_name_in_arg_definition921 = new BitSet(new long[]{0x0000000640000020L});
    public static final BitSet FOLLOW_33_in_arg_definition971 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_property_value_in_arg_definition975 = new BitSet(new long[]{0x0000000440000020L});
    public static final BitSet FOLLOW_30_in_arg_definition1120 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_property_name_in_arg_definition1125 = new BitSet(new long[]{0x0000000640000020L});
    public static final BitSet FOLLOW_33_in_arg_definition1153 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_property_value_in_arg_definition1157 = new BitSet(new long[]{0x0000000440000020L});
    public static final BitSet FOLLOW_34_in_arg_definition1335 = new BitSet(new long[]{0x0000000010000002L});
    public static final BitSet FOLLOW_28_in_arg_definition1381 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_option_comment_in_arg_definition1385 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_NAME_in_arg_name1565 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_STRING_CONSTANT_in_arg_regexp1586 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_NAME_in_property_name1620 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_STRING_CONSTANT_in_property_value1661 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_STRING_CONSTANT_in_option_comment1704 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SECTION_FORMAT_in_args_format_section1734 = new BitSet(new long[]{0x0000001000000020L});
    public static final BitSet FOLLOW_format_clause_in_args_format_section1736 = new BitSet(new long[]{0x0000000810000000L});
    public static final BitSet FOLLOW_28_in_args_format_section1809 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_option_comment_in_args_format_section1813 = new BitSet(new long[]{0x0000000800000000L});
    public static final BitSet FOLLOW_35_in_args_format_section1896 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_format_subclause_in_format_clause1928 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_NAME_in_format_subclause1958 = new BitSet(new long[]{0x000003D000000022L});
    public static final BitSet FOLLOW_36_in_format_subclause1989 = new BitSet(new long[]{0x0000001000000020L});
    public static final BitSet FOLLOW_format_subclause_in_format_subclause1991 = new BitSet(new long[]{0x0000002000000000L});
    public static final BitSet FOLLOW_37_in_format_subclause1993 = new BitSet(new long[]{0x000003D000000022L});
    public static final BitSet FOLLOW_repetition_operator_in_format_subclause2043 = new BitSet(new long[]{0x0000005000000022L});
    public static final BitSet FOLLOW_or_format_subclause_in_format_subclause2069 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_38_in_or_format_subclause2101 = new BitSet(new long[]{0x0000001000000020L});
    public static final BitSet FOLLOW_format_subclause_in_or_format_subclause2105 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_set_in_repetition_operator0 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SECTION_WHERE_in_where_section2179 = new BitSet(new long[]{0x0000000000000022L});
    public static final BitSet FOLLOW_where_clause_in_where_section2182 = new BitSet(new long[]{0x0000000000000022L});
    public static final BitSet FOLLOW_NAME_in_where_clause2218 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_28_in_where_clause2227 = new BitSet(new long[]{0x0000054000200020L});
    public static final BitSet FOLLOW_child_in_where_clause2234 = new BitSet(new long[]{0x0000054800200020L});
    public static final BitSet FOLLOW_35_in_where_clause2263 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_DASH_in_child2284 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_NAME_in_child2288 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_set_in_child2306 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_NAME_in_child2317 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SECTION_FLY_in_fly_section2342 = new BitSet(new long[]{0x0000000000000022L});
    public static final BitSet FOLLOW_fly_rule_in_fly_section2345 = new BitSet(new long[]{0x0000000000000022L});
    public static final BitSet FOLLOW_NAME_in_fly_rule2373 = new BitSet(new long[]{0x0000080000000800L});
    public static final BitSet FOLLOW_condition_in_fly_rule2421 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_43_in_fly_rule2469 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_NAME_in_fly_rule2473 = new BitSet(new long[]{0x0000100000000000L});
    public static final BitSet FOLLOW_44_in_fly_rule2475 = new BitSet(new long[]{0x0000000000000800L});
    public static final BitSet FOLLOW_assignment_rhs_in_fly_rule2479 = new BitSet(new long[]{0x0000000840000000L});
    public static final BitSet FOLLOW_30_in_fly_rule2511 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_NAME_in_fly_rule2530 = new BitSet(new long[]{0x0000100000000000L});
    public static final BitSet FOLLOW_44_in_fly_rule2532 = new BitSet(new long[]{0x0000000000000800L});
    public static final BitSet FOLLOW_assignment_rhs_in_fly_rule2536 = new BitSet(new long[]{0x0000000840000000L});
    public static final BitSet FOLLOW_35_in_fly_rule2570 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_UNCHECKED_CODE_BLOCK_in_condition2616 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_UNCHECKED_CODE_BLOCK_in_assignment_rhs2648 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SECTION_OVERRIDES_in_overrides_section2679 = new BitSet(new long[]{0x0000000000000802L});
    public static final BitSet FOLLOW_override_rule_in_overrides_section2682 = new BitSet(new long[]{0x0000000000000802L});
    public static final BitSet FOLLOW_condition_in_override_rule2714 = new BitSet(new long[]{0x0000080000000000L});
    public static final BitSet FOLLOW_43_in_override_rule2716 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_NAME_in_override_rule2760 = new BitSet(new long[]{0x0000100000000000L});
    public static final BitSet FOLLOW_44_in_override_rule2762 = new BitSet(new long[]{0x0000000000000800L});
    public static final BitSet FOLLOW_assignment_rhs_in_override_rule2766 = new BitSet(new long[]{0x0000000840000000L});
    public static final BitSet FOLLOW_30_in_override_rule2808 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_NAME_in_override_rule2833 = new BitSet(new long[]{0x0000100000000000L});
    public static final BitSet FOLLOW_44_in_override_rule2835 = new BitSet(new long[]{0x0000000000000800L});
    public static final BitSet FOLLOW_assignment_rhs_in_override_rule2839 = new BitSet(new long[]{0x0000000840000000L});
    public static final BitSet FOLLOW_35_in_override_rule2923 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_SECTION_VALIDITY_in_validity_section2952 = new BitSet(new long[]{0x0002200000000802L});
    public static final BitSet FOLLOW_validity_rule_in_validity_section2955 = new BitSet(new long[]{0x0002200000000802L});
    public static final BitSet FOLLOW_standard_validity_rule_in_validity_rule2987 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_requires_validity_rule_in_validity_rule3008 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_exclusive_validity_rule_in_validity_rule3029 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_condition_in_standard_validity_rule3055 = new BitSet(new long[]{0x0000000810000000L});
    public static final BitSet FOLLOW_28_in_standard_validity_rule3115 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_explanation_in_standard_validity_rule3117 = new BitSet(new long[]{0x0000000800000000L});
    public static final BitSet FOLLOW_35_in_standard_validity_rule3238 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_45_in_requires_validity_rule3273 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_28_in_requires_validity_rule3275 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_arg_name_in_requires_validity_rule3277 = new BitSet(new long[]{0x0000400000000000L});
    public static final BitSet FOLLOW_46_in_requires_validity_rule3279 = new BitSet(new long[]{0x0000001000000020L});
    public static final BitSet FOLLOW_requires_expression_in_requires_validity_rule3281 = new BitSet(new long[]{0x0000000810000000L});
    public static final BitSet FOLLOW_28_in_requires_validity_rule3341 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_explanation_in_requires_validity_rule3343 = new BitSet(new long[]{0x0000000800000000L});
    public static final BitSet FOLLOW_35_in_requires_validity_rule3461 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_requires_or_expression_in_requires_expression3497 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_requires_and_expression_in_requires_or_expression3550 = new BitSet(new long[]{0x0000800000000002L});
    public static final BitSet FOLLOW_47_in_requires_or_expression3554 = new BitSet(new long[]{0x0000001000000020L});
    public static final BitSet FOLLOW_requires_and_expression_in_requires_or_expression3556 = new BitSet(new long[]{0x0000800000000002L});
    public static final BitSet FOLLOW_requires_expression_unit_in_requires_and_expression3618 = new BitSet(new long[]{0x0001000000000002L});
    public static final BitSet FOLLOW_48_in_requires_and_expression3622 = new BitSet(new long[]{0x0000001000000020L});
    public static final BitSet FOLLOW_requires_expression_unit_in_requires_and_expression3624 = new BitSet(new long[]{0x0001000000000002L});
    public static final BitSet FOLLOW_arg_name_in_requires_expression_unit3690 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_36_in_requires_expression_unit3726 = new BitSet(new long[]{0x0000001000000020L});
    public static final BitSet FOLLOW_requires_expression_in_requires_expression_unit3728 = new BitSet(new long[]{0x0000002000000000L});
    public static final BitSet FOLLOW_37_in_requires_expression_unit3730 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_49_in_exclusive_validity_rule3791 = new BitSet(new long[]{0x0000000010000000L});
    public static final BitSet FOLLOW_28_in_exclusive_validity_rule3793 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_arg_name_in_exclusive_validity_rule3797 = new BitSet(new long[]{0x0000000040000000L});
    public static final BitSet FOLLOW_30_in_exclusive_validity_rule3865 = new BitSet(new long[]{0x0000000000000020L});
    public static final BitSet FOLLOW_arg_name_in_exclusive_validity_rule3869 = new BitSet(new long[]{0x0000000850000000L});
    public static final BitSet FOLLOW_28_in_exclusive_validity_rule4039 = new BitSet(new long[]{0x0000000000000080L});
    public static final BitSet FOLLOW_explanation_in_exclusive_validity_rule4041 = new BitSet(new long[]{0x0000000800000000L});
    public static final BitSet FOLLOW_35_in_exclusive_validity_rule4176 = new BitSet(new long[]{0x0000000000000002L});
    public static final BitSet FOLLOW_STRING_CONSTANT_in_explanation4230 = new BitSet(new long[]{0x0000000000000002L});

}