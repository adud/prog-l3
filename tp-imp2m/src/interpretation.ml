(*
 *  This file is part of Imp2ML
 *  Copyright (c) 2017 ENS Lyon / Département Informatique
 *  Philippe Audebaud <paudebau at gmail dot com>
 *
 * This software falls under the GNU general public license version 3 or later.
 * It comes WITHOUT ANY WARRANTY WHATSOEVER. For details, see the file LICENSE
 * in the root directory or <http://www.gnu.org/licenses/gpl-3.0.html>.
 *)

open Syntax

(* Interprétation IMP -> ML *)

let ml_of_imp c =
  let vars = vars_of_imp c in
  let return = Ftuple vars in
  let rec loop depth = function
  | Cskip -> return
  | Cassign (x, e) -> Fletin("x",e,return)
  | Cseq (Cassign (x, e), c2) -> Fletin("x",e,loop depth c2)
  | Cseq (c1, c2) -> Fletsin(vars, loop depth c1,loop depth c2)
  | Cifte (b, c1, c2) -> 
  | Cwhiledo (b, c) -> 
  in Fletsin (vars, loop 0 c, return)
