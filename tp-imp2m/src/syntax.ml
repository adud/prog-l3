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

type aoper = | Aadd | Asub | Amul
type aexpr =
  | Acst of int
  | Avar of variable
  | Abin of aoper * aexpr * aexpr

type bcomp = | Beq | Bne | Ble | Blt | Bge | Bgt
type boper = | Band | Bor
type bexpr =
  | Btest of bcomp * aexpr * aexpr
  | Boper of boper * bexpr * bexpr
  | Bneg of bexpr

type imp =
  | Cskip
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


(* Détermination de l'ensemble (non ordonné des variables libres *)

module S = Set.Make(String)

let rec vars_of_aexpr = function
  | Acst _ ->  S.empty
  | Avar x -> S.singleton(x)
  | Abin (_, a, b) -> S.union (vars_of_aexpr a) (vars_of_aexpr b)
and vars_of_bexpr = function
  | Btest (_, a, b) ->  S.union (vars_of_aexpr a) (vars_of_aexpr b)
  | Boper (_, p, q) -> S.union (vars_of_bexpr p) (vars_of_bexpr q)
  | Bneg p -> vars_of_bexpr p
and vars_of_imp = function
  | Cskip -> S.empty
  | Cassign (x, a) -> S.add x (vars_of_aexpr a)
  | Cseq (c1, c2) -> S.union (vars_of_imp c1) (vars_of_imp c2)
  | Cifte (b, c1, c2) -> S.union (vars_of_bexpr b) (S.union (vars_of_imp c1) (vars_of_imp c2))
  | Cwhiledo (b, c) -> S.union (vars_of_bexpr b) (vars_of_imp c)

let vars_of_imp c = S.elements (vars_of_imp c) (* liste ordonnée *)

