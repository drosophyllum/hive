%{
#pragma once
#include "parser.h"

#define YY_DECL extern int yylex()

%}

%option noyywrap

%%
[ \t\n]         ;
[A-Z][a-zA-Z0-9]* { yylval.val = strdup(yytext);return VARIABLE;}
[a-z][a-zA-Z0-9]*    { yylval.val = strdup(yytext); return SYMBOL ;}
\.		{ return DOT; }
"=>"		{ return ARROW; }
"("		{ return BEG; }
")"		{return END;}
","		{return COMA;}
";"		{return SEMI;}
.		;
%%
