(*
 *  This file is part of Imp2ML
 *  Copyright (c) 2017 ENS Lyon / Département Informatique
 *  Philippe Audebaud <paudebau at gmail dot com>
 *
 * This software falls under the GNU general public license version 3 or later.
 * It comes WITHOUT ANY WARRANTY WHATSOEVER. For details, see the file LICENSE
 * in the root directory or <http://www.gnu.org/licenses/gpl-3.0.html>.
 *)

type variable = string
type aoper = Aadd | Asub | Amul
type aexpr = Acst of int | Avar of variable | Abin of aoper * aexpr * aexpr

type bcomp = Beq | Bne | Ble | Blt | Bge | Bgt
type boper = | Band | Bor
type bexpr =
  | Btest of bcomp * aexpr * aexpr
  | Boper of boper * bexpr * bexpr
  | Bneg of bexpr

type imp =
    Cskip
  | Cassign of variable * aexpr
  | Cseq of imp * imp
  | Cifte of bexpr * imp * imp
  | Cwhiledo of bexpr * imp

type tuple = variable list
type ml =
  | Faexpr of aexpr
  | Fbexpr of bexpr
  | Ftuple of tuple
  | Fletin of variable * aexpr * ml
  | Fletsin of tuple * ml * ml
  | Fletrecin of int * tuple * ml * ml
  | Fcall of int * tuple
  | Fifte of bexpr * ml * ml
  (* used by standalone module *)
  | Fcaml of string * tuple * ml

val vars_of_imp : imp -> tuple
