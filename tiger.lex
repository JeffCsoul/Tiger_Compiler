type pos            = int
type lexresult      = Tokens.token

val lineNum         = ErrorMsg.lineNum
val linePos         = ErrorMsg.linePos
val nested_comment  = ref 0
val buff_string     = ref ""
val left_tag        = ref 0
val format_flag     = ref false
val valid_str       = ref true
fun err(p1,p2)      = ErrorMsg.error p1

fun eof()           = let val pos = hd(!linePos) in Tokens.EOF(pos,pos) end


%%
%s COMMENT STRING SLASH SLASH_M;
%%
<INITIAL>"\n"       => (lineNum := !lineNum + 1;
                        linePos := yypos :: !linePos;
                        continue());
<INITIAL>" "        => (continue());
<INITIAL>"\t"       => (continue());

<INITIAL>"type"     => (Tokens.TYPE(yypos, yypos + 4));
<INITIAL>"var"      => (Tokens.VAR(yypos, yypos + 3));
<INITIAL>"function" => (Tokens.FUNCTION(yypos, yypos + 8));
<INITIAL>"break"    => (Tokens.BREAK(yypos, yypos + 5));
<INITIAL>"of"       => (Tokens.OF(yypos, yypos + 2));
<INITIAL>"end"      => (Tokens.END(yypos, yypos + 3));
<INITIAL>"in"       => (Tokens.IN(yypos, yypos + 2));
<INITIAL>"nil"      => (Tokens.NIL(yypos, yypos + 3));
<INITIAL>"let"      => (Tokens.LET(yypos, yypos + 3));
<INITIAL>"do"       => (Tokens.DO(yypos, yypos + 2));
<INITIAL>"to"       => (Tokens.TO(yypos, yypos + 2));
<INITIAL>"for"      => (Tokens.FOR(yypos, yypos + 3));
<INITIAL>"while"    => (Tokens.WHILE(yypos, yypos + 5));
<INITIAL>"else"     => (Tokens.ELSE(yypos, yypos + 4));
<INITIAL>"then"     => (Tokens.THEN(yypos, yypos + 4));
<INITIAL>"if"       => (Tokens.IF(yypos, yypos + 2));
<INITIAL>"array"    => (Tokens.ARRAY(yypos, yypos + 5));

<INITIAL>":="       => (Tokens.ASSIGN(yypos, yypos + 2));
<INITIAL>"|"        => (Tokens.OR(yypos, yypos + 1));
<INITIAL>"&"        => (Tokens.AND(yypos, yypos + 1));
<INITIAL>">="       => (Tokens.GE(yypos, yypos + 2));
<INITIAL>">"        => (Tokens.GT(yypos, yypos + 1));
<INITIAL>"<="       => (Tokens.LE(yypos, yypos + 2));
<INITIAL>"<"        => (Tokens.LT(yypos, yypos + 1));
<INITIAL>"<>"       => (Tokens.NEQ(yypos, yypos + 2));
<INITIAL>"="        => (Tokens.EQ(yypos, yypos + 1));
<INITIAL>"/"        => (Tokens.DIVIDE(yypos, yypos + 1));
<INITIAL>"*"        => (Tokens.TIMES(yypos, yypos + 1));
<INITIAL>"-"        => (Tokens.MINUS(yypos, yypos + 1));
<INITIAL>"+"        => (Tokens.PLUS(yypos, yypos + 1));
<INITIAL>"."        => (Tokens.DOT(yypos, yypos + 1));
<INITIAL>"}"        => (Tokens.RBRACE(yypos, yypos + 1));
<INITIAL>"{"        => (Tokens.LBRACE(yypos, yypos + 1));
<INITIAL>"]"        => (Tokens.RBRACK(yypos, yypos + 1));
<INITIAL>"["        => (Tokens.LBRACK(yypos, yypos + 1));
<INITIAL>")"        => (Tokens.RPAREN(yypos, yypos + 1));
<INITIAL>"("        => (Tokens.LPAREN(yypos, yypos + 1));
<INITIAL>";"        => (Tokens.SEMICOLON(yypos, yypos + 1));
<INITIAL>":"        => (Tokens.COLON(yypos, yypos + 1));
<INITIAL>","        => (Tokens.COMMA(yypos, yypos + 1));
<INITIAL>[a-zA-Z]([a-z0-9A-Z]|"_")*
                    => (Tokens.ID(yytext, yypos, yypos + size yytext));
<INITIAL>[0-9]+     => (let val SOME tempint = Int.fromString(yytext)
                        in
                          Tokens.INT(tempint,
                                     yypos, yypos + size yytext)
                        end);
<INITIAL>"/*"       => (YYBEGIN COMMENT;
                        nested_comment := 1;
                        continue());
<INITIAL>"\""       => (YYBEGIN STRING;
                        buff_string := "";
                        left_tag := yypos;
                        format_flag := true;
                        valid_str := true;
                        continue());

<COMMENT>"/*"       => (nested_comment := !nested_comment + 1;
                        continue());
<COMMENT>"*/"       => (nested_comment := !nested_comment - 1;
                        if (!nested_comment = 0) then
                            YYBEGIN INITIAL
                        else if (!nested_comment < 0) then
                            ErrorMsg.error yypos ("illegal comments")
                        else ();
                        continue());
<COMMENT>.          => (continue());
<COMMENT>"\n"       => (lineNum := !lineNum + 1;
                        linePos := yypos :: !linePos;
                        continue());

<STRING>"\""        => (YYBEGIN INITIAL;
                        if (!format_flag andalso !valid_str)
                          then
                            Tokens.STRING(!buff_string, !left_tag, yypos + 1)
                          else
                            (ErrorMsg.error yypos ("illegal string");
                             Tokens.STRING("", !left_tag, yypos + 1)));
<STRING>"\n"        => (YYBEGIN INITIAL;
                        ErrorMsg.error yypos ("illegal string having \\n");
                        valid_str := false;
                        lineNum := !lineNum + 1;
                        linePos := yypos :: !linePos;
                        Tokens.STRING("", !left_tag, yypos + 1));
<STRING>"\\"        => (YYBEGIN SLASH;
                        continue());
<STRING>.           => (buff_string := !buff_string ^ yytext;
                        continue());

<SLASH>"n"          => (YYBEGIN STRING;
                        buff_string := !buff_string ^ "\n";
                        continue());
<SLASH>"t"          => (YYBEGIN STRING;
                        buff_string := !buff_string ^ "\t";
                        continue());
<SLASH>"\^"[@-_]       => (YYBEGIN STRING;
                        buff_string := !buff_string ^
                          String.str(chr(ord(String.sub(yytext, 1)) - 64));
                        continue());
<SLASH>[0-9][0-9][0-9]
                    => (YYBEGIN STRING;
                        let val SOME tempnum = Int.fromString(yytext)
                        in
                          if tempnum > 255
                            then
                              (ErrorMsg.error yypos ("illegal escape \\" ^
                                                      yytext);
                               valid_str := false)
                            else buff_string := !buff_string ^
                                                String.str(chr(tempnum))
                        end;
                        continue());
<SLASH>"\""         => (YYBEGIN STRING;
                        buff_string := !buff_string ^ "\"";
                        continue());
<SLASH>"\\"         => (YYBEGIN STRING;
                        buff_string := !buff_string ^ "\\";
                        continue());
<SLASH>(" "|"\t"|"\f")
                    => (YYBEGIN SLASH_M;
                        buff_string := !buff_string ^ yytext;
                        format_flag := true;
                        continue());
<SLASH>"\n"         => (YYBEGIN SLASH_M;
                        buff_string := !buff_string ^ "\n";
                        format_flag := true;
                        lineNum := !lineNum + 1;
                        linePos := yypos :: !linePos;
                        continue());
<SLASH>.            => (YYBEGIN SLASH_M;
                        buff_string := !buff_string ^ yytext;
                        format_flag := false;
                        continue());

<SLASH_M>"\n"       => (buff_string := !buff_string ^ "\n";
                        format_flag := true;
                        lineNum := !lineNum + 1;
                        linePos := yypos :: !linePos;
                        continue());
<SLASH_M>(" "|"\t"|"\f")
                    => (buff_string := !buff_string ^ yytext;
                        format_flag := true;
                        continue());
<SLASH_M>"\\"       => (if !format_flag
                          then YYBEGIN STRING
                          else
                            (ErrorMsg.error yypos("illegal format \\f___f\\");
                             YYBEGIN STRING);
                        continue());
<SLASH_M>"\""       => (YYBEGIN INITIAL;
                        ErrorMsg.error yypos("illegal escape");
                        Tokens.STRING("", !left_tag, yypos + 1));
<SLASH_M>.          => (buff_string := !buff_string ^ yytext;
                        continue());


<INITIAL>.          => (ErrorMsg.error yypos ("illegal character " ^ yytext);
                        continue());
