%{
  #include <iostream>
  #include "test.tab.h" 
  using namespace std;
  int line_num = 1;
  namespace SVM_FRONTEND{ 
  }
  #define MODULE_KEYWORD(module) \
        return nullptr;
  extern int yylex();
%}
%option noyywrap
%x COMMENT
%%

[ \t]     ;
"MODULE".*  ;
IVAR   {return IVAR;}
VAR  {return VAR;}
INVAR   {return INVAR;}
FROZENVAR   {return FROZENVAR;}
INVARSPEC   {return INVARSPEC;}
INIT   {return INIT;}
TRANS   {return TRANS;}
READ   {return READ;}
WRITE   {return WRITE;}
ASSIGN   {return ASSIGN;}
CONSTARRAY   {return CONSTARRAY;}
CONSTANTS   {return CONSTANTS;}
FUN   {return FUN;}
TRUE   {return TRUE;}
FALSE   {return FALSE;}
DEFINE {return DEFINE;}
next  {return tok_next;}
init {return tok_init;}
pi {return pi;}
abs {return ABS;}
max {return MAX;}
min {return MIN;}
sin {return SIN;}
cos {return COS;}
exp {return EXP;}
tan {return TAN;}
ln {return ln;}
of  {return of;}
word1 {return word1;}
bool {return BOOL;}
toint   {return TOINT;}
count {return COUNT;}
swconst {return swconst;}
uwconst {return uwconst;}
sizeof {return SIZEOF;}
floor {return FLOOR;}
extend {return extend;}
resize {return resize;}
typeof {return TYPEOF;}
"signed word" {return signed_word;}
"unsigned word" {return unsigned_word;}
"array word"   {return arrayword;}
"array integer"   {return arrayinteger;}
"array" {return array_tok;}
"unsigned"   {return tok_unsigned;}
"signed"   {return tok_signed;}
boolean   {return bool_type;}
real  {return real_type;}
integer   {return integer_type;}
clock   {return clock_type;}
word   {return tok_word;}
set {return set_tok;}
in {return in;}
time {return time_type;}
".." {return TO;}
"(" {return '(';}
")" {return ')';}
"[" {return '[';}
"]" {return ']';}
"{" {return '{';}
"}" {return '}';}
";" {return ';';}
":" {return ':';}
"," {return ',';}
":=" {return ASSIGNSYM;}
"--".*  {cout<<"COMMENT IS HERE" << yytext <<endl;}
0(u|s)(b|d|o|h)[0-9]+_[0-9]+ {return word_value;}
"->"  {return OP_IMPLY;}
"<->"  {return OP_BI;}
"!"  {return '!';}
"::"  {return CONCAT;}
"-"  {return '-';}
"+"  {return '+';}
"*"  {return '*';}
"/"  {return '/'; }
"mod"  {return OP_MOD;}
">>"  {return OP_SHIFTR;}
"<<"  {return OP_SHIFTL;}
"union"  {return UNION;}
"="  {return '=';}
"!="  {return OP_NEQ;}
">"  {return '>';}
"<"  {return '<';}
"<="  {return OP_LTE;}
">="  {return OP_GTE;}
"&"  {return '&';}
"|"  {return '|';}
"xor"  {return OP_XOR;}
"xnor"  {return OP_XNOR;}
"?"  {return IF_ELSE;}
[0-9]+           {return integer_val;}
[0-9]+*\.[0-9_]*([eE][-+]?[0-9_]+)?          {return real_val;}
[a-zA-Z0-9_$]+      {yylval.str = strdup(yytext); return tok_name;}
\n   {line_num++; return ENDL;}
.                {return '.';};

%%