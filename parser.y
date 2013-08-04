%{
#pragma once
#include <stdio.h>

#include "parser.h"
#include "AST.h"
// stuff from flex that bison needs to know about:
extern int yylex();
extern int yyparse(struct Arrow *firstArrow);
extern FILE *yyin;
 
void yyerror(struct Arrow *firstArrow, const char* s);
struct Arrow* parse(FILE *f);
%}

%parse-param {struct Arrow *firstArrow}

// Bison fundamentally works by asking flex to get the next token, which it
// returns as an object of type "yystype".  But tokens could be of any
// arbitrary data type!  So we deal with that in Bison by defining a C union
// holding each of the types of tokens that Flex could return, and have Bison
// use that union instead of "int" for the definition of "yystype":
%union {
	char *val;
	struct Arrow* arr;
	struct Symbol* symb;
}

// define the "terminal symbol" token types I'm going to use (in CAPS
// by convention), and associate each with a field of the union:
%token <val> SYMBOL
%token <val> VARIABLE
%token DOT
%token ARROW
%token BEG
%token END 
%token COMA 
%token SEMI 
%type<arr> hive 
%type<symb> bind
%type<symb> symbol
%type<symb> symbolist
%type<symb> symb
%%
// this is the actual grammar that bison will parse, but for right now it's just
// something silly to echo to the screen what bison gets from flex.  We'll
// make a real one shortly:
hive:
	bind ARROW bind SEMI hive 	{struct Arrow *v = (struct Arrow*) malloc(sizeof(struct Arrow));
				 v->inBind  = $1;
				 v->outBind = $3;
				 v->next    = $5;
			 	 topnode=v;
				 $$=v;
				}
	| bind ARROW bind SEMI	{struct Arrow *v = (struct Arrow*) malloc(sizeof(struct Arrow));
				 v->inBind  = $1;
				 v->outBind = $3;
				 v->next    = NULL;
			 	 topnode=v;
				 $$=v;
				}
	;

bind: 
	symbol bind	{$1->next = $2; $$=$1;
			}
	| symbol  	{$1->next = NULL;
			 $$=$1;		
			}
	;

symbol:  symb BEG symbolist END {$1->children = $3;
				 $$=$1;
				}
	| symb 			{$$ = $1;}
	;

symbolist : symb COMA symbolist	{$1->next = $3; $$ = $1;}
	| symb			{$$=$1;}
	;

symb: SYMBOL DOT VARIABLE 	{struct Symbol *s = (struct Symbol*) malloc(sizeof(struct Symbol));
				 memset((void*)s , 0  , sizeof(struct Symbol));
				 s->name = $3;
				 s->node = $1;
				 s->isVariable = true;
				 $$=s;
				}
	| SYMBOL DOT SYMBOL 	{struct Symbol *s = (struct Symbol*) malloc(sizeof(struct Symbol));
				 memset((void*)s , 0  , sizeof(struct Symbol));
				 s->name = $3;
				 s->node = $1;
				 s->isVariable = false;
				 $$=s;
				}
	;




%%

void yyerror(struct Arrow* firstArrow, const char* s) {
	// might as well halt now:
	exit(-1);
}

struct Arrow* parse(FILE * f){
		yyin = f;
	struct Arrow* a;
	yyparse(a);
	return topnode;
}
