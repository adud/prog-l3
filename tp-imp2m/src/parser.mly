/*
 *  This file is part of Imp2ML
 *  Copyright (c) 2017 ENS Lyon / Département Informatique
 *  Philippe Audebaud <paudebau at gmail dot com>
 *
 * This software falls under the GNU general public license version 3 or later.
 * It comes WITHOUT ANY WARRANTY WHATSOEVER. For details, see the file LICENSE
 * in the root directory or <http://www.gnu.org/licenses/gpl-3.0.html>.
 */

%{

(* Pre parser *)

%}

%token ASSIGN SKIP SEQ WHILE DO DONE IF THEN ELSE FI EOF
%token LPAREN RPAREN
%token ADD SUB MULT
%token AND OR NOT
%token EQ NE GE LE GT LT
%token <string> IDENT
%token <int> INT

%left AND OR
%left SUB ADD
%left MULT
%nonassoc NOT

%start program
%type <Syntax.imp> program

%%

program:
 | commands EOF { $1 }
 ;

aexpr:
 | LPAREN aexpr RPAREN { $2 }
 | INT                 { Syntax.Acst $1 }
 | IDENT               { Syntax.Avar $1}
 | SUB aexpr           { Syntax.Abin (Syntax.Asub,Syntax.Acst 0, $2) }
 | aexpr ADD aexpr     { Syntax.Abin (Syntax.Aadd, $1, $3) }
 | aexpr SUB aexpr     { Syntax.Abin (Syntax.Asub, $1, $3) }
 | aexpr MULT aexpr    { Syntax.Abin (Syntax.Amul, $1, $3) }
 ;

bcomp:
 | EQ  { Syntax.Beq }
 | NE  { Syntax.Bne }
 | LE  { Syntax.Ble }
 | LT  { Syntax.Blt }
 | GE  { Syntax.Bge }
 | GT  { Syntax.Bgt }
 ;

bexpr:
 | LPAREN bexpr RPAREN { $2 }
 | NOT bexpr           { Syntax.Bneg ($2) }
 | aexpr bcomp aexpr   { Syntax.Btest ($2, $1, $3) }
 | bexpr AND bexpr     { Syntax.Boper (Syntax.Band, $1, $3) }
 | bexpr OR bexpr      { Syntax.Boper (Syntax.Bor, $1, $3) }
 ;

command:
 | SKIP                                    { Syntax.Cskip }
 | IDENT ASSIGN aexpr                      { Syntax.Cassign ($1, $3) }
 | IF bexpr THEN commands ELSE commands FI { Syntax.Cifte ($2, $4, $6) }
 | WHILE bexpr DO commands DONE            { Syntax.Cwhiledo ($2, $4) }
 ;

commands :
  | command { $1 }
  | command SEQ commands { Syntax.Cseq ($1, $3) }
  ;

/* Menhir way
commands:
  | cmds = separated_list(SEQ, command) { TODO cmds }
;
 */

%%

(* Post parser *)
