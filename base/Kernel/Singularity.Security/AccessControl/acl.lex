using System;
using Microsoft.Contracts;
%%
%line
%char
%namespace Microsoft.Singularity.Security.AccessControl
%class AclParser
%function NextToken
%type AclToken

%state GROUPNAME

ANY=!
ARC=[^./@\{()*+!\|]+|{ANY}
GN=[^\}]+
LITERAL=[()|\*/\|@]
ESCAPE=[\+\.]
%%

<YYINITIAL> {ARC} {
  String! str = (!)yytext().Substring(0, yytext().Length);
  if (str.Equals("!"))
    {
      return (new AclToken(AclTokenType.Any, str, yychar, yychar + 1));
    }
  else
    {
      return (new AclToken(AclTokenType.Arc, str, yychar, yychar + str.Length));
    }
}

<YYINITIAL> "{" {yybegin(GROUPNAME); return null;}

<GROUPNAME> {GN} {
  String! str =  (!)yytext().Substring(0, yytext().Length);
  return (new AclToken(AclTokenType.GroupName, str, yychar, yychar + str.Length));
}

<GROUPNAME> "}" {yybegin(YYINITIAL); return null;}

<YYINITIAL> {LITERAL} { return (new AclToken(AclTokenType.Literal, yytext(), yychar, yychar+1)); }


<YYINITIAL> {ESCAPE} { return (new AclToken(AclTokenType.Escape, yytext(), yychar, yychar+1)); }

<YYINITIAL> {ANY} { return (new AclToken(AclTokenType.Any, yytext(), yychar, yychar+1)); }

<YYINITIAL> . { return (new AclToken(AclTokenType.Miscellaneous, yytext(), yychar, yychar+1)); }
<GROUPNAME> . { return (new AclToken(AclTokenType.Miscellaneous, yytext(), yychar, yychar+1)); }
