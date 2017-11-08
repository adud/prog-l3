(*
 *  This file is part of Imp2ML
 *  Copyright (c) 2017 ENS Lyon / Département Informatique
 *  Philippe Audebaud <paudebau at gmail dot com>
 *
 * This software falls under the GNU general public license version 3 or later.
 * It comes WITHOUT ANY WARRANTY WHATSOEVER. For details, see the file LICENSE
 * in the root directory or <http://www.gnu.org/licenses/gpl-3.0.html>.
 *)

let template = "(* 
 * This file has been generated automatically with command:
 *   imp2ml -standalone {{ path }}
 *)

{{ code }}
;;

(* #trace {{ ident }};; *)
  
let () =
  if {{ nvars }} + 1 != Array.length Sys.argv then
    Printf.printf \"usage: %s {{ lvars }}\\n\" Sys.argv.(0)
  else
    let args = Array.map int_of_string (Array.sub Sys.argv 1 {{ nvars }}) in
    let ({{ tvars }}) = {{ ident }} ({{ avars }}) in
    Printf.printf \"returns ({{ fmt }})\\n\" {{ lvars }}
"

let ocaml ident vars imp = 
  let ml = Interpretation.ml_of_imp imp in
  let ml = Syntax.Fcaml (ident, vars, ml) in
  Print.string_of_ml "" ml

let string_list_of vars =
  let rec loop = function
    | [] -> ""
    | [x] -> Printf.sprintf "\"%s\"" x
    | x :: l -> Printf.sprintf "\"%s\"; %s" x (loop l)
  in "[" ^ loop vars ^ "]"

let string_tuple_of_args id vars =
  let rec loop n =
    if n >= List.length vars then
      []
    else
      Printf.sprintf "%s.(%d)" id n :: loop (n + 1)
  in String.concat ", " (loop 0)

let ident_re = Str.regexp_string "{{ ident }}"
let path_re = Str.regexp_string "{{ path }}"
and code_re = Str.regexp_string "{{ code }}"
and nvars_re = Str.regexp_string "{{ nvars }}"
and avars_re = Str.regexp_string "{{ avars }}"
and lvars_re = Str.regexp_string "{{ lvars }}"
and tvars_re = Str.regexp_string "{{ tvars }}"
and fmt_re = Str.regexp_string "{{ fmt }}"

let generate_ocaml path imp =
  let ident = "caml" in
  let vars = Syntax.vars_of_imp imp in
  let sml = ocaml ident vars imp in
  let nvars = string_of_int (List.length vars) in
  let avars = string_tuple_of_args "args" vars in
  let fmt = String.concat ", " (List.map (fun x -> x ^ " = %d") vars) in
  (* TODO : find better... *)
  let code = Str.replace_first path_re path template in
  let code = Str.replace_first code_re sml code in
  let code = Str.global_replace ident_re ident code in
  let code = Str.global_replace avars_re avars code in
  let code = Str.global_replace nvars_re nvars code in
  let code = Str.global_replace tvars_re (String.concat ", " vars) code in
  let code = Str.global_replace lvars_re (String.concat " " vars) code in
  let code = Str.global_replace fmt_re fmt code in

  let dst = Filename.chop_extension path ^ ".ml" in
  let fout = open_out dst in
  output_string fout code;
  close_out fout;
  Printf.printf "run as: ocaml %s!\n" dst
