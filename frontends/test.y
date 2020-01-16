%{


    #include<cstdio>
    #include<iostream>
    #include<string>
    #include <map>
    #include <string>
    #include <unordered_map>

    #include "assert.h"
    #include "exceptions.h"
    #include "rts.h"
    #include "smt-switch/smt.h"

      smt::Sort sort_;
      std::string symbol_;
    //#include "encoder.h"
    using namespace std;
    extern int yylex();
    extern int yypasrse();
    extern FILE *yyin;
    extern int line_num;
    void yyerror(const char *s);
%}
%code requires{
  class smvEncoder;
}
%union {
	char *str;
	bool boolean;
}

%token IVAR INVAR VAR FROZENVAR INVARSPEC
%token INPUT OUTPUT INIT TRANS DEFINE CONSTANTS
%token READ WRITE ASSIGN
%token MODULE FUN ASSIGNSYM
%token tok_next tok_init real_val integer_val CONSTARRAY time_type
%token bool_type integer_type real_type clock_type set_tok array_tok
%token <str> tok_name empty word_value
%token <boolean> TRUE FALSE
%token tok_signed tok_unsigned
%token ENDL tok_word of arrayword array arrayinteger
%token CONCAT IF_ELSE TO
%token pi ABS MAX MIN SIN COS EXP TAN ln
%token TYPEOF SIZE
%token word1 BOOL TOINT COUNT swconst uwconst SIZEOF FLOOR extend resize signed_word unsigned_word in

%left OP_NOT
%left OP_CON
%left UNARY_MINUS
%left OP_DIV OP_MUL OP_MOD
%left OP_PLUS OP_MINUS
%left OP_SHIFTR OP_SHIFTL
%left UNION
%left OP_EQ OP_NEQ OP_LT OP_GT OP_LTE OP_GTE
%left OP_AND
%left OP_OR OP_XOR OP_XNOR
%left '+' '!' '-' '*' '/'
%left OP_BI
%right OP_IMPLY

%%
header: 
    ENDL
    | define_decl
    | constants_decl
    | assign_decl
    | ivar_test 
    | var_test
    | init_test
    | trans_test
    | invarspec_test
    | fun_test
    | header ENDL
    | header define_decl
    | header constants_decl
    | header assign_decl
    | header ivar_test
    | header var_test
    | header init_test
    | header trans_test
    | header invarspec_test
    | header fun_test;

define_decl:
    DEFINE define_body ;

define_body: complex_identifier ASSIGNSYM next_expr ';' ENDL
            | define_body complex_identifier ASSIGNSYM next_expr ';' ENDL ;

constants_decl:
    CONSTANTS constants_body ;

constants_body: complex_identifier
            | constants_body ',' complex_identifier ';' ENDL;

assign_decl: ASSIGN assign_list ;

assign_list: assign ';' ENDL
            | assign_list assign ';' ENDL;

assign: complex_identifier
        | tok_init '('complex_identifier ')' ASSIGNSYM next_expr;
        | tok_next '('complex_identifier ')' ASSIGNSYM next_expr;

ivar_test:
    IVAR ENDL ivar_list next_line {
       //cout<< "bison finds an IVAR"<<endl;
    } |
    IVAR ENDL ivar_list{
      //cout << "bison found an IVAR" << endl;
    } | ivar_test ivar_list next_line
      | ivar_test ivar_list;


ivar_list:
    tok_name ':' type_identifier ';' ENDL{
       // cout << "find a real ivar" << endl;

    };

var_test:
    VAR ENDL var_list next_line{
      //cout << "bison found a VAR" << endl;
    } | var_test var_list next_line;
      | VAR ENDL var_list;
      | var_test var_list;
    ;

var_list:
    tok_name ':' type_identifier ';' ENDL{
        symbol_ = tok_name;
         cout << "find a real var" << symbol_ << endl;
        //sort_ = type_check(type_identifier);
        //Term state = rts_.make_state(tok_name, type_identifier);
    };

next_line: ENDL;

init_test: INIT tok_name '=' constant ';' ENDL next_line
           | INIT tok_name '=' constant ';' ENDL;

trans_test: TRANS next_formula ';' ENDL next_line
            | TRANS next_formula ';' ENDL;
            

invarspec_test: INVARSPEC basic_expr '=' basic_expr ';' ENDL next_line
                | INVARSPEC basic_expr '=' basic_expr ';' ENDL;
                | INVARSPEC basic_expr '=' basic_expr ';';

fun_test: FUN ENDL basic_expr ':' integer_type '*' integer_type OP_IMPLY word_type ';' ENDL next_line;
          | FUN ENDL basic_expr ':' integer_type '*' integer_type OP_IMPLY word_type ';' ENDL ;

next_formula: next_expr '=' expr 
              | basic_expr '=' expr;

expr:       basic_expr
            | next_expr;

basic_expr: constant 
            | tok_name
            | pi
            | ABS '(' basic_expr ')'
            | MAX '(' basic_expr ',' basic_expr ')'
            | MIN '(' basic_expr ',' basic_expr ')'
            | SIN '(' basic_expr ')'
            | COS '(' basic_expr ')'
            | EXP '(' basic_expr ')'
            | TAN '(' basic_expr ')'
            | ln '(' basic_expr ')'
            | '!' basic_expr
            | basic_expr '&' basic_expr
            | basic_expr '|' basic_expr
            | basic_expr OP_XOR basic_expr
            | basic_expr OP_XNOR basic_expr
            | basic_expr OP_IMPLY basic_expr
            | basic_expr OP_BI basic_expr
            | basic_expr '=' basic_expr
            | basic_expr OP_NEQ basic_expr
            | basic_expr '<' basic_expr
            | basic_expr '>' basic_expr
            | basic_expr OP_LTE basic_expr
            | basic_expr OP_GTE basic_expr
            | '-' basic_expr
            | basic_expr '+' basic_expr
            | basic_expr '-' basic_expr
            | basic_expr '*' basic_expr
            | basic_expr '/' basic_expr
            | basic_expr OP_MOD basic_expr
            | basic_expr OP_SHIFTR basic_expr
            | basic_expr OP_SHIFTL basic_expr
            | basic_expr '[' integer_val ']'
            | basic_expr '[' basic_expr ':' basic_expr ']'
            | basic_expr CONCAT basic_expr
            | word1 '(' basic_expr ')'
            | BOOL '(' basic_expr ')'
            | TOINT '(' basic_expr ')'
            | COUNT '(' basic_expr_list ')'
            | swconst '(' basic_expr ')'
            | uwconst '(' basic_expr ')'
            | tok_signed '(' basic_expr ')'
            | tok_unsigned '(' basic_expr ')'
            | SIZEOF '(' basic_expr ')'
            | FLOOR '(' basic_expr ')'
            | extend '(' basic_expr ')'
            | resize '(' basic_expr ')'
            | signed_word sizev '(' basic_expr ')'
            | unsigned_word sizev '(' basic_expr ')'
            | basic_expr UNION '(' basic_expr ')'
            |'{' set_body_expr '}'
            | basic_expr in basic_expr
            | basic_expr IF_ELSE basic_expr ':' basic_expr          
          | WRITE'('basic_expr','basic_expr','basic_expr')'
          | READ '(' basic_expr ',' basic_expr ')'
          | CONSTARRAY '(' TYPEOF '(' tok_name ')' ',' basic_expr ')' 
          | CONSTARRAY '(' arrayword sizev of type_identifier ',' basic_expr ')' 
          | CONSTARRAY '(' arrayinteger of type_identifier ',' basic_expr ')' 
          | next_expr;

next_expr: tok_next '(' basic_expr ')';

simple_expr: basic_expr;

basic_expr_list: basic_expr
                | basic_expr_list ',' basic_expr;

set_body_expr: basic_expr
                | set_body_expr ',' basic_expr;
          
constant: boolean_constant
          | integer_constant
          | real_constant
          | word_value
          | clock_constant
          | symbolic_constant
          | range_constant;

boolean_constant: TRUE
                | FALSE;

integer_constant: integer_val;
real_constant: real_val;
range_constant: integer_val TO integer_val;
clock_constant: time_type;
symbolic_constant: complex_identifier;

complex_identifier: tok_name
                    | complex_identifier '.' tok_name;

type_identifier: real_type
                | integer_type 
                | bool_type
                | clock_type
                | word_type
                | array_type
                | integer_val TO integer_val
                | array integer_val TO integer_val of type_identifier;

word_type: signed_word sizev
          | unsigned_word sizev
          | tok_word sizev;

array_type: arrayword sizev of type_identifier
          | arrayinteger of type_identifier
          | array of type_identifier;

sizev:
    '[' integer_val ']'{
        //cout << "find a size" << endl;
    };
%%

int main(int, char** argv) {
  
  // open a file handle to a particular file:
  FILE *myfile = fopen(argv[1], "r");
  // make sure it's valid:
  if (!myfile) {
    cout << "NO input file!" << endl;
    return -1;
  }
  // set lex to read from it instead of defaulting to STDIN:
  yyin = myfile;

  yyparse();
}

void yyerror(const char *s) {
  cout << "parse error at line "<<line_num << " message:" << s << endl;
  // might as well halt now:
  exit(-1);
}
