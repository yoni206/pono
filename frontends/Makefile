test.tab.c test.tab.h: test.y
	bison -d test.y

lex.yy.c: test.l test.tab.h
	flex test.l

test: lex.yy.c test.tab.c test.tab.h
	g++ -std=c++11 -I../utils/ -I../core/ -I../deps/smt-switch/local/include -L../build/ -L../deps/smt-switch/local/lib test.tab.c lex.yy.c -o test -lcosa2 -lsmt-switch -lsmt-switch-btor

clean:
	rm test