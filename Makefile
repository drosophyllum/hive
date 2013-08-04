Cm     = gcc
CFLAGS = -g -O0 -std=gnu99 -pthread

READLINE_LIB = ./readline-6.2/libreadline.a
HISTORY_LIB = ./readline-6.2/libhistory.a
TERMCAP_LIB = -ltermcap


YACC   = bison
YFLAGS = -dv -bhive

LEX    = flex
LFLAGS = -t

SRC    = parser.y lexer.lex
OBJ    = parser.o lexer.o AST.o 


all:	hive

hive:	$(OBJ)
	$(CC) $(CFLAGS) $(OBJ) -o $@ $(READLINE_LIB) $(HISTORY_LIB) $(TERMCAP_LIB) -lm 

lexer.o: lexer.c

lexer.c: lexer.lex
	$(LEX) $(LFLAGS) lexer.lex > lexer.c

parser.c: parser.y
	$(YACC) $(YFLAGS) parser.y
	@mv hive.tab.c parser.c
	@mv hive.tab.h parser.h

clean:
	rm *.o	
