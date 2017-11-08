(*
 *  This file is part of Imp2ML
 *  Copyright (c) 2017 ENS Lyon / Département Informatique
 *  Philippe Audebaud <paudebau at gmail dot com>
 *
 * This software falls under the GNU general public license version 3 or later.
 * It comes WITHOUT ANY WARRANTY WHATSOEVER. For details, see the file LICENSE
 * in the root directory or <http://www.gnu.org/licenses/gpl-3.0.html>.
 *)

let parse path =
  try
    let lexbuf = Lexing.from_channel (open_in path) in
    Parser.program Lexer.next_token lexbuf
  with
  | Parsing.Parse_error -> failwith (Printf.sprintf "Parsing eror line %d !" !Lexer.curr_line)
(*  | e -> failwith (Printf.printf "uncaught exception %s\n" (Printexc.to_string e)) *)

let source = ref ""
let standalone = ref false

let _ =
  if not !Sys.interactive then
    begin
      try
        Arg.parse
          ["-standalone", Arg.Unit (fun () -> standalone := true), "Generate runnable Ocaml code"]
          (fun s -> source := s)
          "usage: main <source>" ;
        let imp = parse !source in
        if !standalone then
          let _ = Standalone.generate_ocaml !source imp in
          print_string "done.\n"
        else
          let ml = Interpretation.ml_of_imp imp in
          let sml = Print.string_of_ml "" ml in
          Printf.printf "%s\n" sml
      with
      | e -> Printf.printf "uncaught exception %s\n" (Printexc.to_string e) 
    end
