test.tab.c test.tab.h: test.y
	bison -d test.y

lex.yy.c: test.l test.tab.h
	flex test.l

test: lex.yy.c test.tab.c test.tab.h
	g++ test.tab.c lex.yy.c -o test

clean:
	rm test