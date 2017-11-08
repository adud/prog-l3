(*
 *  This file is part of Imp2ML
 *  Copyright (c) 2017 ENS Lyon / Département Informatique
 *  Philippe Audebaud <paudebau at gmail dot com>
 *
 * This software falls under the GNU general public license version 3 or later.
 * It comes WITHOUT ANY WARRANTY WHATSOEVER. For details, see the file LICENSE
 * in the root directory or <http://www.gnu.org/licenses/gpl-3.0.html>.
 *)

{
  open Lexing
  open Parser

  exception Stop

  let keywords_dict = Hashtbl.create 23 

  let _ = 
    Hashtbl.add keywords_dict "while" WHILE;
    Hashtbl.add keywords_dict "do" DO;
    Hashtbl.add keywords_dict "done" DONE;

    Hashtbl.add keywords_dict "skip" SKIP;

    Hashtbl.add keywords_dict "if" IF;
    Hashtbl.add keywords_dict "then" THEN;
    Hashtbl.add keywords_dict "else" ELSE;
    Hashtbl.add keywords_dict "fi" FI;

    Hashtbl.add keywords_dict "and" AND;
    Hashtbl.add keywords_dict "or" OR;
    Hashtbl.add keywords_dict "not" NOT

  let keyword_orelse_ident s = 
    try Hashtbl.find keywords_dict s 
    with Not_found -> IDENT(s) 

  let curr_level = ref 0
  let curr_line = ref 1
}


let letter = ['a'-'z' 'A'-'Z']
let digit = ['0'-'9']
let identifier = letter (letter | digit | '_' | '.')*
let integer = ['0'-'9']+
let space = [' ' '\t']

rule next_token = parse
    space+  { next_token lexbuf }
  | '\n'    { incr curr_line; next_token lexbuf }
  | eof     { EOF }

  | identifier { keyword_orelse_ident (lexeme lexbuf) }
  | integer    { INT (int_of_string (lexeme lexbuf)) }

  | "//"    { eol_comment lexbuf }            
  | "/*"    { curr_level := 1; comment lexbuf }

  | ';'     { SEQ }
  | "<-"    { ASSIGN }

  | "("     { LPAREN }
  | ")"     { RPAREN }

  | "=="    { EQ }
  | "<>"    { NE }
  | "<="    { LE }
  | '<'     { LT }
  | ">="    { GE }
  | '>'     { GT }

  | '+'     { ADD }
  | '-'     { SUB }
  | '*'     { MULT }

and eol_comment = parse
  | '\n'    { incr curr_line; next_token lexbuf }
  | _       { eol_comment lexbuf }

and comment = parse
  | "*/"    { decr curr_level; if !curr_level = 0 then next_token lexbuf else comment lexbuf }
  | "/*"    { incr curr_level; comment lexbuf }
  | _       { comment lexbuf }

{

  (* Post lexer *)

}
