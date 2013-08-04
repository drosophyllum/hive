#pragma once

typedef enum { False = 0, True = 1 } Bool;
#define bool Bool
#define true True
#define false False

struct Arrow	 	{
			struct Symbol* inBind ;	
			struct Symbol* outBind ;
			struct Arrow* next;
			};


struct Symbol		{
			char* node ;
			char* name ;
			bool   isVariable ; 
			struct Symbol* children ;
			struct Symbol* next ;
			};

extern struct Arrow* topnode ;
